use darling::FromDeriveInput;
use proc_macro::{self, TokenStream};
use quote::quote;
use syn::{self, parse_macro_input, TypeParamBound, WherePredicate};

#[derive(FromDeriveInput, Default)]
#[darling(default, attributes(kernel))]
struct KernelOpts {
    kernel: Option<syn::Expr>,
}

#[proc_macro_derive(KernelFunctions, attributes(kernel))]
pub fn kernel_functions_derive(input: TokenStream) -> TokenStream {
    // Construct a representation of the code as a syntax tree to manipulate
    let ast = parse_macro_input!(input);
    let opts = KernelOpts::from_derive_input(&ast)
        .expect("Wrong options for KernelFunctions derive macro");

    if let Some(kernel) = opts.kernel.as_ref() {
        match kernel {
            syn::Expr::Field(_) => (),
            _ => panic!("kernel attribute must be a struct field access"),
        }
    }

    // Build the trait implementation
    impl_kernel_functions_macro(ast, opts)
}

fn impl_kernel_functions_macro(mut ast: syn::DeriveInput, opts: KernelOpts) -> TokenStream {
    let name = &ast.ident;

    // Check whether type has generic named O that is assumed to be the oracle
    #[cfg(feature = "interrupt-oracle")]
    {
        let mut found_oracle = false;
        for gen in ast.generics.type_params() {
            if gen.ident == "O" {
                found_oracle = true;
                break;
            }
        }
        if !found_oracle {
            panic!("KernelFunctions derive needs a generic for the oracle type called 'O'")
        }
    }

    let kernel = if let Some(kernel) = opts.kernel {
        kernel
    } else {
        let ts: TokenStream = "self.kernel".parse().unwrap();
        parse_macro_input!(ts)
    };

    ast.generics.make_where_clause();
    let obounds = "where";
    #[cfg(feature = "interrupt-oracle")]
    let obounds = format!("{} O: rustsat::solvers::Interrupt,", obounds);
    let obounds: TokenStream = obounds.parse().unwrap();
    let obounds: syn::WhereClause = parse_macro_input!(obounds);
    ast.generics
        .where_clause
        .as_mut()
        .unwrap()
        .predicates
        .extend(obounds.predicates);

    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    quote! {
        impl #impl_generics KernelFunctions for #name #ty_generics #where_clause {
            fn pareto_front(&self) -> crate::types::ParetoFront {
                self.pareto_front.clone()
            }

            fn stats(&self) -> crate::Stats {
                #kernel.stats
            }

            fn attach_logger<L: crate::WriteSolverLog + 'static>(&mut self, logger: L) {
                #kernel.attach_logger(logger)
            }

            fn detach_logger(&mut self) -> Option<Box<dyn crate::WriteSolverLog>> {
                #kernel.detach_logger()
            }

            fn interrupter(&mut self) -> crate::solver::Interrupter {
                #kernel.interrupter()
            }
        }
    }
    .into()
}

#[derive(FromDeriveInput, Default)]
#[darling(default, attributes(solve))]
struct SolveOpts {
    bounds: Option<syn::WhereClause>,
    extended_stats: bool,
    oracle_stats: bool,
}

#[proc_macro_derive(Solve, attributes(solve))]
pub fn solve_derive(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input);
    let kopts = KernelOpts::from_derive_input(&ast)
        .expect("Wrong options for KernelFunctions derive macro");
    let sopts = SolveOpts::from_derive_input(&ast).expect("Wrong options for Solve derive macro");

    if let Some(kernel) = kopts.kernel.as_ref() {
        match kernel {
            syn::Expr::Field(_) => (),
            _ => panic!("kernel attribute must be a struct field access"),
        }
    }

    // Build the trait implementation
    impl_solve_macro(ast, kopts, sopts)
}

fn impl_solve_macro(mut ast: syn::DeriveInput, kopts: KernelOpts, sopts: SolveOpts) -> TokenStream {
    let name = &ast.ident;

    // Check whether type has generic named O that is assumed to be the oracle
    let mut found_oracle = false;
    for gen in ast.generics.type_params() {
        if gen.ident == "O" {
            found_oracle = true;
            break;
        }
    }
    if !found_oracle {
        panic!("Solve derive needs a generic for the oracle type called 'O'")
    }

    let kernel = if let Some(kernel) = kopts.kernel {
        kernel
    } else {
        let ts: TokenStream = "self.kernel".parse().unwrap();
        parse_macro_input!(ts)
    };

    ast.generics.make_where_clause();
    let obounds = "where";
    #[cfg(feature = "interrupt-oracle")]
    let obounds = format!("{} O: rustsat::solvers::Interrupt,", obounds);
    #[cfg(feature = "phasing")]
    let obounds = format!("{} O: rustsat::solvers::PhaseLit,", obounds);
    #[cfg(feature = "sol-tightening")]
    let obounds = format!(
        "{} O: rustsat::solvers::FlipLit + rustsat::solvers::FreezeVar,",
        obounds
    );
    #[cfg(feature = "limit-conflicts")]
    let obounds = format!("{} O: rustsat::solvers::LimitConflicts,", obounds);
    let obounds: TokenStream = obounds.parse().unwrap();
    let obounds: syn::WhereClause = parse_macro_input!(obounds);
    ast.generics
        .where_clause
        .as_mut()
        .unwrap()
        .predicates
        .extend(obounds.predicates);
    if let Some(add_bounds) = sopts.bounds {
        ast.generics
            .where_clause
            .as_mut()
            .unwrap()
            .predicates
            .extend(add_bounds.predicates)
    }

    // If O: SolveStats is satisfied, add oracle stats
    // (this doesn't actually check that this bound is on O)
    let mut oracle_stats = false;
    if !sopts.extended_stats {
        if let Some(ref where_clause) = ast.generics.where_clause {
            for pred in where_clause.predicates.iter() {
                if let WherePredicate::Type(typ) = pred {
                    for bound in typ.bounds.iter() {
                        if let TypeParamBound::Trait(tb) = bound {
                            if tb.path.segments.last().unwrap().ident == "SolveStats" {
                                oracle_stats = true;
                            }
                        }
                    }
                }
            }
        }
    }

    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    if sopts.extended_stats {
        quote! {
            impl #impl_generics Solve for #name #ty_generics #where_clause {
                fn solve(&mut self, limits: Limits) -> Result<bool, Termination> {
                    #kernel.start_solving(limits);
                    self.alg_main()?;
                    Ok(true)
                }

                fn all_stats(&self) -> (crate::Stats, Option<rustsat::solvers::SolverStats>, Option<Vec<crate::EncodingStats>>) {
                    use crate::ExtendedSolveStats;
                    (#kernel.stats, Some(self.oracle_stats()),
                    Some(self.encoding_stats()))
                }
            }
        }
    } else if oracle_stats {
        quote!{
            impl #impl_generics Solve for #name #ty_generics #where_clause {
                fn solve(&mut self, limits: Limits) -> Result<bool, Termination> {
                    #kernel.start_solving(limits);
                    self.alg_main()?;
                    Ok(true)
                }

                fn all_stats(&self) -> (crate::Stats, Option<rustsat::solvers::SolverStats>, Option<Vec<crate::EncodingStats>>) {
                    use rustsat::solvers::SolveStats;
                    (#kernel.stats, Some(#kernel.oracle.stats()), None)
                }
            }
        }
    } else {
        quote!{
            impl #impl_generics Solve for #name #ty_generics #where_clause {
                fn solve(&mut self, limits: Limits) -> Result<bool, Termination> {
                    #kernel.start_solving(limits);
                    self.alg_main()?;
                    Ok(true)
                }

                fn all_stats(&self) -> (crate::Stats, Option<rustsat::solvers::SolverStats>, Option<Vec<crate::EncodingStats>>) {
                    (#kernel.stats, None, None)
                }
            }
        }
    }
    .into()
}

#[proc_macro_attribute]
pub fn oracle_bounds(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let ast: syn::Item = parse_macro_input!(item);
    let impl_block = match ast {
        syn::Item::Impl(impl_block) => impl_block,
        _ => panic!("oracle_bounds attribute can only be used on impl blocks"),
    };

    insert_oracle_bounds(impl_block)
}

fn insert_oracle_bounds(mut impl_block: syn::ItemImpl) -> TokenStream {
    // Check whether type has generic named O that is assumed to be the oracle
    let mut found_oracle = false;
    for gen in impl_block.generics.type_params() {
        if gen.ident == "O" {
            found_oracle = true;
            break;
        }
    }
    if !found_oracle {
        panic!("oracle_bounds attribute needs a generic for the oracle type called 'O'")
    }

    let obounds = "where";
    #[cfg(feature = "interrupt-oracle")]
    let obounds = format!("{} O: rustsat::solvers::Interrupt,", obounds);
    #[cfg(feature = "phasing")]
    let obounds = format!("{} O: rustsat::solvers::PhaseLit,", obounds);
    #[cfg(feature = "sol-tightening")]
    let obounds = format!(
        "{} O: rustsat::solvers::FlipLit + rustsat::solvers::FreezeVar,",
        obounds
    );
    #[cfg(feature = "limit-conflicts")]
    let obounds = format!("{} O: rustsat::solvers::LimitConflicts,", obounds);
    let obounds: TokenStream = obounds.parse().unwrap();
    let obounds: syn::WhereClause = parse_macro_input!(obounds);

    impl_block.generics.make_where_clause();
    impl_block
        .generics
        .where_clause
        .as_mut()
        .unwrap()
        .predicates
        .extend(obounds.predicates);

    quote! { #impl_block }.into()
    //}
}

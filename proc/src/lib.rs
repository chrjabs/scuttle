use darling::FromDeriveInput;
use proc_macro::{self, TokenStream};
use quote::quote;
use syn::{self, parse_macro_input};

#[proc_macro_derive(KernelFunctions)]
pub fn kernel_functions_derive(input: TokenStream) -> TokenStream {
    // Construct a representation of the code as a syntax tree to manipulate
    let ast = parse_macro_input!(input);

    // Build the trait implementation
    impl_kernel_functions_macro(ast)
}

fn impl_kernel_functions_macro(mut ast: syn::DeriveInput) -> TokenStream {
    let name = &ast.ident;

    // Check whether type has generic named O that is assumed to be the oracle
    #[cfg(feature = "oracle-term")]
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

    ast.generics.make_where_clause();
    let obounds = "where";
    #[cfg(feature = "oracle-term")]
    let obounds = format!("{} O: rustsat::solvers::Terminate<'static>,", obounds);
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
                self.kernel.pareto_front.clone()
            }

            fn stats(&self) -> crate::Stats {
                self.kernel.stats
            }

            fn attach_logger<L: crate::WriteSolverLog + 'static>(&mut self, logger: L) {
                self.kernel.attach_logger(logger)
            }

            fn detach_logger(&mut self) -> Option<Box<dyn crate::WriteSolverLog>> {
                self.kernel.detach_logger()
            }

            fn attach_terminator(&mut self, term_cb: fn() -> rustsat::solvers::ControlSignal) {
                self.kernel.attach_terminator(term_cb)
            }

            fn detach_terminator(&mut self) {
                self.kernel.detach_terminator()
            }
        }
    }
    .into()
}

#[derive(FromDeriveInput, Default)]
#[darling(default, attributes(solve))]
struct SolveOpts {
    bounds: Option<syn::WhereClause>,
}

#[proc_macro_derive(Solve, attributes(solve))]
pub fn solve_derive(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input);
    let opts = SolveOpts::from_derive_input(&ast).expect("Wrong options for Solve derive macro");

    // Build the trait implementation
    impl_solve_macro(ast, opts)
}

fn impl_solve_macro(mut ast: syn::DeriveInput, opts: SolveOpts) -> TokenStream {
    let name = &ast.ident;

    // Check whether type has generic named O that is assumed to be the oracle
    #[cfg(feature = "oracle-term")]
    {
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
    }

    ast.generics.make_where_clause();
    let obounds = "where";
    #[cfg(feature = "oracle-term")]
    let obounds = format!("{} O: rustsat::solvers::Terminate<'static>,", obounds);
    #[cfg(feature = "phasing")]
    let obounds = format!("{} O: rustsat::solvers::PhaseLit,", obounds);
    #[cfg(feature = "sol-tightening")]
    let obounds = format!("{} O: rustsat::solvers::FlipLit,", obounds);
    let obounds: TokenStream = obounds.parse().unwrap();
    let obounds: syn::WhereClause = parse_macro_input!(obounds);
    ast.generics
        .where_clause
        .as_mut()
        .unwrap()
        .predicates
        .extend(obounds.predicates);
    if let Some(add_bounds) = opts.bounds {
        ast.generics
            .where_clause
            .as_mut()
            .unwrap()
            .predicates
            .extend(add_bounds.predicates)
    }

    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    quote! {
        impl #impl_generics Solve for #name #ty_generics #where_clause {
            fn solve(&mut self, limits: Limits) -> Result<(), Termination> {
                self.kernel.start_solving(limits);
                self.alg_main()
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
    //#[cfg(all(not(feature = "phasing"), not(feature = "sol-tightening")))]
    //{
    //    return quote! { #impl_block }.into()
    //}
    //#[cfg(any(feature = "phasing", feature = "sol-tightening"))]
    //{
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
    #[cfg(feature = "phasing")]
    let obounds = format!("{} O: rustsat::solvers::PhaseLit,", obounds);
    #[cfg(feature = "sol-tightening")]
    let obounds = format!("{} O: rustsat::solvers::FlipLit,", obounds);
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

use darling::FromDeriveInput;
use proc_macro::{self, TokenStream};
use quote::quote;
use syn::{self, parse_macro_input};

#[proc_macro_derive(KernelFunctions)]
pub fn kernel_functions_derive(input: TokenStream) -> TokenStream {
    // Construct a representation of the code as a syntax tree to manipulate
    let ast = syn::parse(input).unwrap();

    // Build the trait implementation
    impl_kernel_functions_macro(ast)
}

fn impl_kernel_functions_macro(ast: syn::DeriveInput) -> TokenStream {
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

    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();
    #[cfg(feature = "oracle-term")]
    let gen = if where_clause.is_some() {
        quote! {
            impl #impl_generics KernelFunctions for #name #ty_generics #where_clause, O: Terminate<'static> {
                fn pareto_front(&self) -> ParetoFront {
                    self.kernel.pareto_front.clone()
                }

                fn stats(&self) -> Stats {
                    self.kernel.stats
                }

                fn attach_logger<L: WriteSolverLog + 'static>(&mut self, logger: L) {
                    self.kernel.attach_logger(logger)
                }

                fn detach_logger(&mut self) -> Option<Box<dyn WriteSolverLog>> {
                    self.kernel.detach_logger()
                }

                fn attach_terminator(&mut self, term_cb: fn() -> ControlSignal) {
                    self.kernel.attach_terminator(term_cb)
                }

                fn detach_terminator(&mut self) {
                    self.kernel.detach_terminator()
                }
            }
        }
    } else {
        quote! {
            impl #impl_generics KernelFunctions for #name #ty_generics where O: Terminate<'static> {
                fn pareto_front(&self) -> ParetoFront {
                    self.kernel.pareto_front.clone()
                }

                fn stats(&self) -> Stats {
                    self.kernel.stats
                }

                fn attach_logger<L: WriteSolverLog + 'static>(&mut self, logger: L) {
                    self.kernel.attach_logger(logger)
                }

                fn detach_logger(&mut self) -> Option<Box<dyn WriteSolverLog>> {
                    self.kernel.detach_logger()
                }

                fn attach_terminator(&mut self, term_cb: fn() -> ControlSignal) {
                    self.kernel.attach_terminator(term_cb)
                }

                fn detach_terminator(&mut self) {
                    self.kernel.detach_terminator()
                }
            }
        }
    };
    #[cfg(not(feature = "oracle-term"))]
    let gen = quote! {
        impl #impl_generics KernelFunctions for #name #ty_generics #where_clause {
            fn pareto_front(&self) -> ParetoFront {
                self.kernel.pareto_front.clone()
            }

            fn stats(&self) -> Stats {
                self.kernel.stats
            }

            fn attach_logger<L: WriteSolverLog + 'static>(&mut self, logger: L) {
                self.kernel.attach_logger(logger)
            }

            fn detach_logger(&mut self) -> Option<Box<dyn WriteSolverLog>> {
                self.kernel.detach_logger()
            }

            fn attach_terminator(&mut self, term_cb: fn() -> ControlSignal) {
                self.kernel.attach_terminator(term_cb)
            }

            fn detach_terminator(&mut self) {
                self.kernel.detach_terminator()
            }
        }
    };
    gen.into()
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

fn impl_solve_macro(ast: syn::DeriveInput, opts: SolveOpts) -> TokenStream {
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

    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();
    assert!(where_clause.is_none(), "Solve derive macro does not support where clauses");
    let add_where = opts.bounds.as_ref();

    #[cfg(feature = "oracle-term")]
    let gen = if add_where.is_some() {
        quote! {
            impl #impl_generics Solve for #name #ty_generics #add_where, O: Terminate<'static> {
                fn solve(&mut self, limits: Limits) -> Result<(), Termination> {
                    self.kernel.start_solving(limits);
                    self.alg_main()
                }
            }
        }
    } else {
        quote! {
            impl #impl_generics Solve for #name #ty_generics where O: Terminate<'static> {
                fn solve(&mut self, limits: Limits) -> Result<(), Termination> {
                    self.kernel.start_solving(limits);
                    self.alg_main()
                }
            }
        }
    };
    #[cfg(not(feature = "oracle-term"))]
    let gen = quote! {
        impl #impl_generics Solve for #name #ty_generics #where_clause #add_where {
            fn solve(&mut self, limits: Limits) -> Result<(), Termination> {
                self.kernel.start_solving(limits);
                self.alg_main()
            }
        }
    };
    gen.into()
}

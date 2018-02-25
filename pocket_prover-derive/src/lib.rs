//! # pocket_prover-derive
//!
//! Derive procedural macros for `pocket_prover`.
//!
//! Example:
//!
//! ```ignore
//! #[macro_use]
//! extern crate pocket_prover_derive;
//! extern crate pocket_prover;
//!
//! use pocket_prover::Construct;
//!
//! #[derive(Construct)]
//! pub struct Foo {
//!     pub a: u64,
//!     pub b: u64,
//! }
//! ```
//!
//! Since `pocket_prover` uses only `u64`,
//! it is the only valid concrete field type.
//!
//! The macro supports generic arguments, assuming that
//! the inner type implements `Construct`:
//!
//! ```ignore
//! #[derive(Construct)]
//! pub struct Bar<T = ()> {
//!     pub foo: T,
//!     pub a: u64,
//!     pub b: u64,
//! }
//! ```

extern crate proc_macro;
extern crate syn;
#[macro_use]
extern crate quote;

use proc_macro::{TokenStream};
use syn::{
    Body, Ident, VariantData, PolyTraitRef, Ty, TyParamBound,
    TraitBoundModifier, WherePredicate, WhereBoundPredicate
};
use quote::Tokens;

#[proc_macro_derive(Construct)]
pub fn construct(input: TokenStream) -> TokenStream {
    // Construct a string representation of the type definition
    let s = input.to_string();

    // Parse the string representation
    let ast = syn::parse_derive_input(&s).unwrap();

    // Build the impl
    let gen = impl_construct(&ast);

    // Return the generated impl
    gen.parse().unwrap()
}

fn impl_construct(ast: &syn::DeriveInput) -> quote::Tokens {
    if let Body::Struct(ref body) = ast.body {
        let name = &ast.ident;
        let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

        // Get field identifier and type for all struct fields.
        let fields: Vec<(_, Ty)> = if let &VariantData::Struct(ref fields) = body {
            fields.iter()
                .map(|field| (
                    field.ident.as_ref().unwrap(),
                    field.ty.clone(),
                )).collect()
        } else {
            panic!("Expected struct fields");
        };

        // Add constraints and compute offsets.
        let mut where_clause = where_clause.clone();
        let mut offsets = Tokens::new();
        let mut i = 0;
        let mut ns = vec![];
        for &(_, ref ty) in &fields {
            let ty_ident = if let &Ty::Path(_, ref parameters) = ty {
                parameters.segments[0].ident.clone()
            } else {
                panic!("Could not find type identifier.")
            };
            if ty_ident != &Ident::new("u64") {
                // Add `T: Construct` constraint.
                where_clause.predicates.push(WherePredicate::BoundPredicate(WhereBoundPredicate {
                    bound_lifetimes: vec![],
                    bounded_ty: ty.clone(),
                    bounds: vec![TyParamBound::Trait(PolyTraitRef {
                        bound_lifetimes: vec![],
                        trait_ref: Ident::new("Construct").into()
                    }, TraitBoundModifier::None)]
                }));
                offsets.append(
                    format!("let n{} = <{} as Construct>::n();", i, ty_ident)
                );
                i += 1;
            } else {
                ns.push(i);
            }
        }

        // Map arguments to struct fields.
        let mut field_tokens = Tokens::new();
        let mut i = 0;
        for &(ref field, ref ty) in &fields {
            field_tokens.append(field);
            field_tokens.append(":");
            let ty_ident = if let &Ty::Path(_, ref parameters) = ty {
                parameters.segments[0].ident.clone()
            } else {
                panic!("Could not find type identifier.")
            };
            if ty_ident == &Ident::new("u64") {
                field_tokens.append("vs[");
                if ns[i] != 0 {
                    field_tokens.append(format!("n{}+", ns[i]-1));
                }
                field_tokens.append(&format!("{}", i));
                field_tokens.append("]");
                i += 1;
            } else {
                field_tokens.append("Construct::construct(vs)");
            }
            field_tokens.append(",");
        }

        quote! {
            impl #impl_generics Construct for #name #ty_generics #where_clause {
                fn construct(vs: &[u64]) -> Self {
                    #offsets
                    #name {
                        #field_tokens
                    }
                }
            }
        }
    } else {panic!("Must be a struct.")}
}

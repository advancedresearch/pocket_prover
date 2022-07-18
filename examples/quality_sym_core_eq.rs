/*

This example shows that, for equality of homotopy equivalence:

- In the case of distinct value symbols, the strong symmetric core axiom is necessary
- In the case of identical value symbols, the weak symmetryc core axiom is sufficient

*/

use pocket_prover::*;

fn main() {
    println!("Distinct value symbols: {}", measure(10, || prove!(&mut |a, b, c, d| {
        imply(
            and!(
                ps_sym_core_eq(a, b, c, d),
                imply(a, c),
                imply(b, d),
            ),
            eq(hom_eq(2, a, b), hom_eq(2, c, d))
        )
    })));

    println!("Identical value symbols: {}", measure(10, || prove!(&mut |a, c, d| {
        imply(
            and!(
                ps_sym_core(a, a, c, d),
                imply(a, c),
                imply(a, d),
            ),
            eq(hom_eq(2, a, a), hom_eq(2, c, d))
        )
    })));
}

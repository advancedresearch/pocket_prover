/*

This example shows that when the strong version of
the path semantical core axiom is used,
equality of quality propagates to values of types.

Quality here might be thought of as identification of symbols.

The strong version of the core axiom assumes
that when types are identified, their values can be identified.
The weak version of the core axiom only assumes
that when values are identified, their types can be identified.

*/

use pocket_prover::*;

fn main() {
    println!("{}", measure(10, || prove!(&mut |a0, b0, a1, b1, c, d| {
        imply(
            and(
                ps_core_eq(a0, b0, c, d),
                ps_core_eq(a1, b1, c, d),
            ),
            imply(
                and!(
                    imply(a0, c),
                    imply(b0, d),
                    imply(a1, c),
                    imply(b1, d),
                ),
                eq(qual(a0, b0), qual(a1, b1))
            )
        )
    })));
}

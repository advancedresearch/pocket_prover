/*

A propositional type is a type where
all members are equal.

The equality between members are forced
by asserting membership.

Propositional types are homotopy level 1.

*/

use pocket_prover::*;

fn main() {
    println!("{}", measure(1, || prove!(&mut |a, b, x| {
        imply(
            and!(
                is_prop(x, a, b),
                imply(a, x),
                imply(b, x),
            ),
            eq(a, b)
        )
    })))
}

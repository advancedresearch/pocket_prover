/*

A set type is a type where
when two members are equal, they have the same properties.

Set types are homotopy level 2.

*/

use pocket_prover::*;

fn main() {
    println!("{}", measure(1, || prove!(&mut |a, b, x| {
        imply(
            and!(
                is_set(x, a, b),
                imply(a, x),
                imply(b, x),
                eq(a, b)
            ),
            hom_eq(2, a, b)
        )
    })))
}

/*

A groupoid type is a type where
when two members are equal, they have the same set properties.
This means that when two morphisms are equal,
they have the same properties, mapping to same objects.

Homotopy equivalence of level 2 between two groupoids
means that there is a functor with inverse mapping
between the two groupoids.
Since this implies that each pair of morphisms are equal,
it means that the two groupoids are the same up to isomorphism,
which is a homotopy equivalence of level 3.

Groupoid types are homotopy level 3.

*/

use pocket_prover::*;

fn main() {
    println!("{}", measure(1, || prove!(&mut |a, b, x| {
        imply(
            and!(
                is_groupoid(x, a, b),
                imply(a, x),
                imply(b, x),
                hom_eq(2, a, b)
            ),
            hom_eq(3, a, b)
        )
    })))
}

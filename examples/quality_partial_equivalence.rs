/*

A partial equivalence is symmetric and transitive,
but not necessarily reflexive.

    Symmetry: true
    Transitivity: true
    Reflexivity: false

Path semantical quality is a partial equivalence relation.

*/

use pocket_prover::*;

fn main() {
    println!("Symmetry: {}", measure(10, || prove!(&mut |a, b| {
        eq(q(a, b), q(b, a))
    })));

    println!("Transitivity: {}", measure(10, || prove!(&mut |a, b, c| {
        imply(
            and(
                q(a, b),
                q(b, c)
            ),
            q(a, c)
        )
    })));

    println!("Reflexivity: {}", measure(10, || prove!(&mut |a| {
        q(a, a)
    })));
}

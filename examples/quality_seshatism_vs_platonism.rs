/*

There are two forms of Platonism,
one where self-quality is assumed directly (`a ~~ a`),
and one where other-quality is assumed (`a ~~ b`).
These forms of Platonism are called Loop Witness
and Product Witness respectively.
Since both the Loop and Product Witnesses implies
self-quality, this means Platonism can be thought of
as some way of proving self-quality (`a ~~ a`).

The self-inquality is Seshatism (`!(a ~~ a)`).

For more information about Seshatism,
see paper https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/seshatism.pdf

You can also look up "Seshatism vs Platonism"
on the summary page about Avatar Extensions:
https://advancedresearch.github.io/avatar-extensions/summary.html#seshatism-vs-platonism

*/

use pocket_prover::*;

fn main() {
    println!("Self-quality from Product Witness: {}", measure(10, || prove!(&mut |a, b| {
        imply(
            q(a, b),
            and(q(a, a), q(b, b))
        )
    })));

    println!("Other-inquality from Seshatism: {}", measure(10, || prove!(&mut |a, b| {
        imply(
            not(q(a, a)),
            not(q(a, b))
        )
    })));

    println!("Excluded Middle of Seshatism vs Platonism: {}", measure(10, || prove!(&mut |a| {
        or(not(q(a, a)), q(a, a))
    })));
}

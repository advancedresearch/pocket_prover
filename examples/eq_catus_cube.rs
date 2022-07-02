/*

Proves the analogue of Eq-Catuskoti but for cube.

For more information about the Eq-Catuskoti theorem,
see https://advancedresearch.github.io/quality/summary.html#psq---path-semantical-quantum-propositional-logic.

*/

use pocket_prover::*;

fn main() {
    println!("{}", prove!(&mut |a, b, c| {
        eq(
            and(eq(a, b), eq(a, c)),
            or!(
                and(aq(a, b), aq(a, c)),
                and(aq(a, b), cq(a, c)),
                and(cq(a, b), aq(a, c)),
                and(cq(a, b), cq(a, c)),
                and(cq(b, a), cq(c, a)),
                and(cq(b, a), q(a, c)),
                and(q(a, b), cq(c, a)),
                and(q(a, b), q(a, c)),
            )
        )
    }))
}

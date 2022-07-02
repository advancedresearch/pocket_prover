/*

Demonstrates the analogue of the Index Theorem in PSQ.

For more information about the Index Theorem,
see https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/index-theorem.pdf.

*/

use pocket_prover::*;

fn main() {
    println!("PSL: {}", prove!(&mut |(tr, fa, i, one), (b, n)| {
        imply(
            and!(
                eq(and(b, not(i)), fa),
                eq(and(b, i), tr),
                eq(and(n, i), one)
            ),
            eq(tr, one)
        )
    }));

    println!("PSQ: {}", measure(1000, || prove!(&mut |tr, fa, i, one, b, n| {
        imply(
            and!(
                ps_core(and(b, not(i)), fa, b, n),
                q(and(b, not(i)), fa),
                q(and(b, i), tr),
                q(and(n, i), one)
            ),
            q(tr, one)
        )
    })));
}

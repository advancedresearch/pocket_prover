/*

This example shows that both PSL and PSQ give
same answers to what happens when `a : (t1 & t2)`.

When the core axiom of path semantics holds for `t1`
and `t2` individually `(t1, t2)`, they are indistinguishable
with respect to path semantical quality.

When the core axiom of path semantics holds only for
`t1 & t2` as a single proposition, they are
distinguishable by equality.

*/

use pocket_prover::*;

fn main() {
    println!("PSL: {}", prove!(&mut |
        (a, b), (t1, t2, u)
    | {
        imply(
            and!(
                imply(a, and(t1, t2)),
                imply(a, u),
                eq(a, b)
            ),
            and!(
                eq(t1, t2)
            )
        )
    }));

    println!("PSQ (t1, t2): {}", measure(100, || prove!(&mut |
        a, b, t1, t2, u
    | {
        imply(
            and!(
                imply(a, and(t1, t2)),
                imply(a, u),
                eq(a, b),
                imply(eq(a, b), q(a, b)),
                ps_core(a, b, t1, u),
                ps_core(a, b, t2, u),
            ),
            and!(
                q(t1, t2)
            )
        )
    })));

    println!("PSL (t1 & t2): {}", prove!(&mut |
        (a, b, t1, t2), (x, u)
    | {
        imply(
            and!(
                imply(a, x),
                eq(x, and(t1, t2)),
                imply(a, u),
                eq(a, b)
            ),
            and!(
                eq(t1, t2)
            )
        )
    }));

    println!("PSQ (t1 & t2): {}", measure(100, || prove!(&mut |
        a, b, t1, t2, u
    | {
        imply(
            and!(
                imply(a, and(t1, t2)),
                imply(a, u),
                eq(a, b),
                imply(eq(a, b), q(a, b)),
                ps_core(a, b, and(t1, t2), u),
            ),
            and!(
                eq(t1, t2)
            )
        )
    })));
}

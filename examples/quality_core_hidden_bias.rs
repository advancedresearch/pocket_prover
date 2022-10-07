/*

This example shows that quality `x ~~ y`
with `ps_core(x, y, a, b)`,
causes "bias" of `!x => ~a` in classical logic.

One can think of this bias as a pressure toward
thinking about symbols as propositionally "positive"
in some sense. Although symbols in themselves do not
need to mean literally truth, they can often
communicate implicitly that the intentionality of
the speaker is directed toward something like truth.

This happens because the negation of `x` causes
unintentional inference, a kind of "inference without control".
The natural tendency of treating symbols as biased
toward propositional truth helps guarding reasoning
and make it safer, more robust against errors.

*/

use pocket_prover::*;

fn main() {
    println!("{}", measure(100, || prove!(&mut |
        a, b, x, y,
    | {
        imply(
            and!(
                ps_core(x, y, a, b),
                q(x, y)
            ),
            and!(
                imply(not(x), qu(a)),
            )
        )
    })));
}

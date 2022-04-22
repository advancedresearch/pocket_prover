/*

This example shows that when self-quality is aligned,
quality is lifted to equality.

*/

use pocket_prover::*;

fn main() {
    println!("Entanglement: {}", prove!(&mut |a, b, c| {
        imply(
            and!(eq(q(a, a), q(c, c)), eq(eq(a, b), eq(b, c))),
            eq(q(a, b), q(b, c))
        )
    }));
}

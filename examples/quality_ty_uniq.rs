use pocket_prover::*;

fn main() {
    println!("PSL: {}", prove!(&mut |
        (a, b), (t, u)
    | {
        imply(
            and!(
                imply(a, t),
                imply(a, u),
                eq(a, b)
            ),
            and!(
                eq(t, u)
            )
        )
    }));

    println!("PSQ: {}", measure(100, || prove!(&mut |
        a, b, t, u
    | {
        imply(
            and!(
                imply(a, t),
                imply(a, u),
                eq(a, b),
                imply(eq(a, b), q(a, b)),
                ps_core(a, b, t, u),
            ),
            and!(
                eq(t, u)
            )
        )
    })));
}

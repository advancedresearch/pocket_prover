use pocket_prover::*;

fn main() {
    println!("PSL: {}", prove!(&mut |
        (a, b), (t, u)
    | {
        imply(
            and!(
                imply(a, t),
                imply(b, u),
                not(eq(t, u)),
            ),
            and!(
                not(eq(a, b))
            )
        )
    }));

    println!("PSQ: {}", measure(100, || prove!(&mut |
        a, b, t, u
    | {
        imply(
            and!(
                imply(a, t),
                imply(b, u),
                not(eq(t, u)),
                imply(eq(a, b), q(a, b)),
                ps_core(a, b, t, u),
            ),
            and!(
                not(eq(a, b))
            )
        )
    })));
}

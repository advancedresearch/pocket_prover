use pocket_prover::*;

fn main() {
    println!("Path semantics: {}", measure(1, || prove!(&mut |a, b, c, d| {
        imply(
            and!(
                ps_core(a, b, c, d),
                imply(a, c),
                imply(b, d)
            ),
            imply(qual(a, b), qual(c, d))
        )
    })));
}

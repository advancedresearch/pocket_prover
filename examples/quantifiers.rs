extern crate pocket_prover;

use pocket_prover::*;

fn main() {
    println!("Quantfiers:");

    // Create some predicates for testing.
    // This is needed to check proofs for different kinds of predicates.
    // For our purposes, we only need `T`, `F` and something in between.
    // This works because the proofs only use a single predicate and no
    // combinations of predicates, and the predicates does not depend
    // on any variable besides the argument.
    let ps: Vec<fn(u8) -> u64> = vec![
        |_: u8| T,
        |_: u8| F,
        |x: u8| prop(x > 5),
    ];
    println!("  universal instantiation (UI): {}", ps.iter().all(|p| {
        all(&|c: u8| imply(
            all(&|x: u8| p(x)),
            p(c)
        )) == T
    }));

    println!("  universal generalization (UG): {}", ps.iter().all(|p| {
        imply(
            all(&|c: u8| p(c)),
            all(&|x: u8| p(x))
        ) == T
    }));

    println!("  existential instantiation (EI): {}", ps.iter().all(|p| {
        all(&|c: u8| imply(
            p(c),
            any(&|x: u8| p(x))
        )) == T
    }));

    println!("  existential generalization (EG): {}", ps.iter().all(|p| {
        imply(
            any(&|c: u8| p(c)),
            any(&|x: u8| p(x))
        ) == T
    }));
}

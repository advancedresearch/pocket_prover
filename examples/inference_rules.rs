extern crate pocket_prover;

use pocket_prover::*;

fn main() {
    println!("Inference rules:");
    // Truth value can be derived from any premise.
    println!("  true-conclusion: {}", prove!(&mut |a| imply(
        a,
        T
    )));
    // Anything can be derived from a false premise.
    println!("  false-premise: {}", prove!(&mut |a| imply(
        F,
        a
    )));

    println!("  modus-ponens: {}", prove!(&mut |p, q| imply(
        and(
            imply(p, q),
            p,
        ),
        q
    )));
    println!("  modus-tollens: {}", prove!(&mut |p, q| imply(
        and(
            imply(p, q),
            not(q)
        ),
        not(p)
    )));
    println!("  hypothetical-syllogism: {}", prove!(&mut |p, q, r| imply(
        and(
            imply(p, q),
            imply(q, r),
        ),
        imply(p, r)
    )));
    println!("  disjunctive-syllogism: {}", prove!(&mut |p, q| imply(
        and(
            or(p, q),
            not(p),
        ),
        q
    )));
    println!("  addition: {}", prove!(&mut |p, q| imply(
        p,
        or(p, q)
    )));
    println!("  simplification: {}", prove!(&mut |p, q| imply(
        and(p, q),
        p
    )));
    println!("  conjunction: {}", prove!(&mut |p, q| imply(
        and(
            p,
            q,
        ),
        and(p, q)
    )));
    println!("  resolution: {}", prove!(&mut |p, q, r| imply(
        and(
            or(not(p), r),
            or(p, q),
        ),
        or(q, r)
    )));
}

/*

This example shows that the Creation Theorem is not a tautology
in the model of path semantical quality that resembles quantum logic.

This means that this model of quality gives rise to a new logic:

   Path Semantical Quantum Propositional Logic (PSQ)

*/

use pocket_prover::*;

fn main() {
    println!("Creation Theorem: {}", measure(10, || prove!(&mut |a, b, a2, b2| {
        creation(a, b, a2, b2)
    })));

    println!("");
    for i in 1..10 {
        for _ in 0..50 {
            if measure(i, || prove!(&mut |a, b, c, d| creation(a, b, c, d))) {
                print!("1");
            } else {
                print!("0");
            }
        }
        println!("");
    }
    println!("");

    println!("Creation Theorem with EqQ: {}", measure(10, || prove!(&mut |a, b, a2, b2| {
        creation_with_eqq(a, b, a2, b2)
    })));

    println!("");
    for i in 1..10 {
        for _ in 0..50 {
            if measure(i, || prove!(&mut |a, b, c, d| creation_with_eqq(a, b, c, d))) {
                print!("1");
            } else {
                print!("0");
            }
        }
        println!("");
    }
}

pub fn creation(a: u64, b: u64, a2: u64, b2: u64) -> u64 {
    imply(
        and!(
            ps_core(a, b, a2, b2),
            not(a),
            imply(b, b2),
        ),
        imply(a2, b2)
    )
}

pub fn creation_with_eqq(a: u64, b: u64, a2: u64, b2: u64) -> u64 {
    imply(
        and!(
            imply(eq(a, b), q(a, b)),
            ps_core(a, b, a2, b2),
            not(a),
            imply(b, b2),
        ),
        imply(a2, b2)
    )
}

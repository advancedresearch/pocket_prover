extern crate pocket_prover;

use pocket_prover::*;

fn main() {
    println!("If logic is false, then logic is true:");
    println!("(T -> F) -> (T -> T)");
    println!("Result: {}", prove!(&mut |_a| {
        imply(imply(T, F), imply(T, T))
    }));
    println!("");
    println!("However, the opposite is not true:");
    println!("(T -> T) -> (T -> F)");
    println!("Result: {}", prove!(&mut |_a| {
        imply(imply(T, T), imply(T, F))
    }));
    println!("");
    println!("Can prove that if logic is true, then is not true that logic is false:");
    println!("(T -> T) -> not(T -> F)");
    println!("Result: {}", prove!(&mut |_a| {
        imply(imply(T, T), not(imply(T, F)))
    }));
    println!("");
    println!("Combining the above shows to show that logic must be true:");
    println!("( (T -> F) -> (T -> T) ) & ( (T -> T) -> not(T -> F) )");
    println!("------------------------------------------------------");
    println!("T -> T");
    println!("Result: {}", prove!(&mut |_a| {
        imply(
            and(
                imply(imply(T, F), imply(T, T)),
                imply(imply(T, T), not(imply(T, F)))
            ),
            imply(T, T)
        )
    }));
    println!("");
    println!("Actually, we are only asserting that true implies true.");
    println!("Still, the same thing happens for all proofs.");
    println!("It just becomes clearer when the proof depends on no variables.");
}

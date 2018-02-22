extern crate pocket_prover;

use pocket_prover::*;

fn main() {
    println!("Socrates is mortal: {}", prove3(&mut |man, mortal, socrates| {
        // Using `imply` because we want to prove an inference rule.
        imply(
            // Premises.
            and(
                // All men are mortal.
                imply(man, mortal),
                // Socrates is a man.
                imply(socrates, man),
            ),

            // Conclusion.
            imply(socrates, mortal)
        )
    }));
}

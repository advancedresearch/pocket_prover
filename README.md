# pocket_prover
A fast, brute force, automatic theorem prover for first order logic

- For generic automated theorem proving, see [monotonic_solver](https://github.com/advancedresearch/monotonic_solver)
- For a debuggable SAT solver, see [debug_sat](https://github.com/advancedresearch/debug_sat)

```rust
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
```

### Motivation

The motivation is to provide the analogue of a "pocket calculator",
but for logic, therefore called a "pocket prover".

This library uses an approach that is simple to implement from scratch in a low level language.

This is useful in cases like:

- Study logic without the hurdle of doing manual proofs
- Checking your understanding of logic
- Verify that logicians are wizards and not lizards
- Due to a series of unfortunate events, you got only 24 hours to learn logic and just need the gist of it
- Memorizing source code for situations like [The Martian](http://www.imdb.com/title/tt3659388/)
- A tiny mistake and the whole planet blows up (e.g. final decisions before the AI singularity and you need to press the right buttons)

In addition this library can be used to create extensible logical systems.
For more information, see the `Prove` trait.

### Implementation

This library uses brute-force to check proofs, instead of relying on axioms of logic.

64bit CPUs are capable of checking logical proofs of 6 arguments (booleans)
in O(1), because proofs can be interpreted as tautologies (true for all input)
and `2^6 = 64`.

This is done by replacing `bool` with `u64` and organizing inputs
using bit patterns that simulate a truth table of 6 arguments.

To extend to 10 arguments, `T` and `F` are used to alternate the 4 extra arguments.
To extend to N arguments, recursive calls are used down to less than 10 arguments.

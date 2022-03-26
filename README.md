# pocket_prover
A fast, brute force, automatic theorem prover for first order logic

- For generic automated theorem proving, see [monotonic_solver](https://github.com/advancedresearch/monotonic_solver)
- For a debuggable SAT solver, see [debug_sat](https://github.com/advancedresearch/debug_sat)

```rust
extern crate pocket_prover;

use pocket_prover::*;

fn main() {
    println!("Socrates is mortal: {}", prove!(&mut |man, mortal, socrates| {
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

### Path Semantical Logic

*Notice! Path Semantical Logic is at early stage of research.*

This library has experimental support for a subset of [Path Semantical Logic](https://github.com/advancedresearch/path_semantics/blob/master/sequences.md#path-semantical-logic).
Implementation is based on paper [Faster Brute Force Proofs](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/faster-brute-force-proofs.pdf).

Path Semantical Logic separates propositions into levels,
such that an equality between two propositions in level N+1,
propagates into equality between uniquely associated propositions in level N.

For example, if `f` has level 1 and `x` has level 0,
then `imply(f, x)` associates `x` uniquely with `f`,
such that the core axiom of [Path Semantics](https://github.com/advancedresearch/path_semantics)
is satisfied.

This library has currently only support for level 1 and 0.
These functions are prefixed with `path1_`.

The macros `count!` and `prove!` will automatically expand
to `path1_count!` and `path1_prove!`.

Each function takes two arguments, consisting of tuples of propositions, e.g. `(f, g), (x, y)`.
Arbitrary number of arguments is supported.

```rust
extern crate pocket_prover;

use pocket_prover::*;

fn main() {
    println!("=== Path Semantical Logic ===");
    println!("The notation `f(x)` means `x` is uniquely associated with `f`.");
    println!("For more information, see the section 'Path Semantical Logic' in documentation.");
    println!("");

    print!("(f(x), g(y), h(z), f=g ⊻ f=h) => (x=y ∨ x=z): ");
    println!("{}\n", prove!(&mut |(f, g, h), (x, y, z)| {
        imply(
            and!(
                imply(f, x),
                imply(g, y),
                imply(h, z),
                xor(eq(f, g), eq(f, h))
            ),
            or(eq(x, y), eq(x, z))
        )
    }));

    print!("(f(x), g(y), f=g => h, h(z)) => (x=y => z): ");
    println!("{}\n", prove!(&mut |(f, g, h), (x, y, z)| {
        imply(
            and!(
                imply(f, x),
                imply(g, y),
                imply(eq(f, g), h),
                imply(h, z)
            ),
            imply(eq(x, y), z)
        )
    }));
}
```

### Path Semantical Quality

Pocket-Prover has a model of [Path Semantical Quality](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/path-semantical-quality.pdf)
that resembles quantum logic.

To write `x ~~ y` you use `q(x, y)` or `qual(x, y)`.

`q(x, x)` is the same as `qubit(x)`.
`q(x, y)` where `x` and `y` are symbolic distinct is the same as `T`.

A qubit is a kind of "superposition".
One can also think about it as introducing a new argument `qubit(x)` that depends on `x`.

Since qubits can collide with other propositions,
one must repeat measurements e.g. using `measure` to get classical states.
However, sometimes one might wish to amplify quantum states, using `amplify` or `amp`.

To use quality with path semantics, one should use `ps_core`.
Path Semantical Logic is designed for equality, not quality.

```rust
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
```

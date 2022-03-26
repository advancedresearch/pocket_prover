#![deny(missing_docs)]

//! # pocket_prover
//! A fast, brute force, automatic theorem prover for first order logic
//!
//! - For generic automated theorem proving, see [monotonic_solver](https://github.com/advancedresearch/monotonic_solver)
//! - For a debuggable SAT solver, see [debug_sat](https://github.com/advancedresearch/debug_sat)
//!
//! ```rust
//! extern crate pocket_prover;
//!
//! use pocket_prover::*;
//!
//! fn main() {
//!     println!("Socrates is mortal: {}", prove!(&mut |man, mortal, socrates| {
//!         // Using `imply` because we want to prove an inference rule.
//!         imply(
//!             // Premises.
//!             and(
//!                 // All men are mortal.
//!                 imply(man, mortal),
//!                 // Socrates is a man.
//!                 imply(socrates, man),
//!             ),
//!
//!             // Conclusion.
//!             imply(socrates, mortal)
//!         )
//!     }));
//! }
//! ```
//!
//! ### Motivation
//!
//! The motivation is to provide the analogue of a "pocket calculator",
//! but for logic, therefore called a "pocket prover".
//!
//! This library uses an approach that is simple to implement from scratch in a low level language.
//!
//! This is useful in cases like:
//!
//! - Study logic without the hurdle of doing manual proofs
//! - Checking your understanding of logic
//! - Verify that logicians are wizards and not lizards
//! - Due to a series of unfortunate events, you got only 24 hours to learn logic and just need the gist of it
//! - Memorizing source code for situations like [The Martian](http://www.imdb.com/title/tt3659388/)
//! - A tiny mistake and the whole planet blows up (e.g. final decisions before the AI singularity and you need to press the right buttons)
//!
//! In addition this library can be used to create extensible logical systems.
//! For more information, see the `Prove` trait.
//!
//! ### Implementation
//!
//! This library uses brute-force to check proofs, instead of relying on axioms of logic.
//!
//! 64bit CPUs are capable of checking logical proofs of 6 arguments (booleans)
//! in O(1), because proofs can be interpreted as tautologies (true for all input)
//! and `2^6 = 64`.
//!
//! This is done by replacing `bool` with `u64` and organizing inputs
//! using bit patterns that simulate a truth table of 6 arguments.
//!
//! To extend to 10 arguments, `T` and `F` are used to alternate the 4 extra arguments.
//! To extend to N arguments, recursive calls are used down to less than 10 arguments.
//!
//! ### Path Semantical Logic
//!
//! *Notice! Path Semantical Logic is at early stage of research.*
//!
//! This library has experimental support for a subset of [Path Semantical Logic](https://github.com/advancedresearch/path_semantics/blob/master/sequences.md#path-semantical-logic).
//! Implementation is based on paper [Faster Brute Force Proofs](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/faster-brute-force-proofs.pdf).
//!
//! Path Semantical Logic separates propositions into levels,
//! such that an equality between two propositions in level N+1,
//! propagates into equality between uniquely associated propositions in level N.
//!
//! For example, if `f` has level 1 and `x` has level 0,
//! then `imply(f, x)` associates `x` uniquely with `f`,
//! such that the core axiom of [Path Semantics](https://github.com/advancedresearch/path_semantics)
//! is satisfied.
//!
//! This library has currently only support for level 1 and 0.
//! These functions are prefixed with `path1_`.
//!
//! The macros `count!` and `prove!` will automatically expand
//! to `path1_count!` and `path1_prove!`.
//!
//! Each function takes two arguments, consisting of tuples of propositions, e.g. `(f, g), (x, y)`.
//! Arbitrary number of arguments is supported.
//!
//! ```rust
//! extern crate pocket_prover;
//!
//! use pocket_prover::*;
//!
//! fn main() {
//!     println!("=== Path Semantical Logic ===");
//!     println!("The notation `f(x)` means `x` is uniquely associated with `f`.");
//!     println!("For more information, see the section 'Path Semantical Logic' in documentation.");
//!     println!("");
//!
//!     print!("(f(x), g(y), h(z), f=g ⊻ f=h) => (x=y ∨ x=z): ");
//!     println!("{}\n", prove!(&mut |(f, g, h), (x, y, z)| {
//!         imply(
//!             and!(
//!                 imply(f, x),
//!                 imply(g, y),
//!                 imply(h, z),
//!                 xor(eq(f, g), eq(f, h))
//!             ),
//!             or(eq(x, y), eq(x, z))
//!         )
//!     }));
//!
//!     print!("(f(x), g(y), f=g => h, h(z)) => (x=y => z): ");
//!     println!("{}\n", prove!(&mut |(f, g, h), (x, y, z)| {
//!         imply(
//!             and!(
//!                 imply(f, x),
//!                 imply(g, y),
//!                 imply(eq(f, g), h),
//!                 imply(h, z)
//!             ),
//!             imply(eq(x, y), z)
//!         )
//!     }));
//! }
//! ```

pub mod extract;

pub use qual as q;
pub use amplify as amp;

/// An AND relation of variable arguments.
#[macro_export]
macro_rules! and(
    ($x0:expr $(,)?) => {$x0};
    ($x0:expr, $x1:expr $(,)?) => {
        and($x0, $x1)
    };
    ($x0:expr, $x1:expr, $x2:expr $(,)?) => {
        and3($x0, $x1, $x2)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr $(,)?) => {
        and4($x0, $x1, $x2, $x3)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr $(,)?) => {
        and5($x0, $x1, $x2, $x3, $x4)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr, $x5:expr $(,)?) => {
        and6($x0, $x1, $x2, $x3, $x4, $x5)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr, $x5:expr, $x6:expr $(,)?) => {
        and7($x0, $x1, $x2, $x3, $x4, $x5, $x6)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr, $x5:expr, $x6:expr, $x7:expr $(,)?) => {
        and8($x0, $x1, $x2, $x3, $x4, $x5, $x6, $x7)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr,
     $x5:expr, $x6:expr, $x7:expr, $x8:expr $(,)?) => {
        and9($x0, $x1, $x2, $x3, $x4, $x5, $x6, $x7, $x8)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr,
     $x5:expr, $x6:expr, $x7:expr, $x8:expr, $x9:expr $(,)?) => {
        and10($x0, $x1, $x2, $x3, $x4, $x5, $x6, $x7, $x8, $x9)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr,
     $x5:expr, $x6:expr, $x7:expr, $x8:expr, $x9:expr, $($y:expr),+ $(,)?) => {
        and(
            and10($x0, $x1, $x2, $x3, $x4, $x5, $x6, $x7, $x8, $x9),
            and!($($y),+)
        )
    };
);

/// An OR relation of variable arguments.
#[macro_export]
macro_rules! or(
    ($x0:expr $(,)?) => {$x0};
    ($x0:expr, $x1:expr $(,)?) => {
        or($x0, $x1)
    };
    ($x0:expr, $x1:expr, $x2:expr $(,)?) => {
        or3($x0, $x1, $x2)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr $(,)?) => {
        or4($x0, $x1, $x2, $x3)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr $(,)?) => {
        or5($x0, $x1, $x2, $x3, $x4)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr, $x5:expr $(,)?) => {
        or6($x0, $x1, $x2, $x3, $x4, $x5)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr, $x5:expr, $x6:expr $(,)?) => {
        or7($x0, $x1, $x2, $x3, $x4, $x5, $x6)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr, $x5:expr, $x6:expr, $x7:expr $(,)?) => {
        or8($x0, $x1, $x2, $x3, $x4, $x5, $x6, $x7)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr,
     $x5:expr, $x6:expr, $x7:expr, $x8:expr $(,)?) => {
        or9($x0, $x1, $x2, $x3, $x4, $x5, $x6, $x7, $x8)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr,
     $x5:expr, $x6:expr, $x7:expr, $x8:expr, $x9:expr $(,)?) => {
        or10($x0, $x1, $x2, $x3, $x4, $x5, $x6, $x7, $x8, $x9)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr,
     $x5:expr, $x6:expr, $x7:expr, $x8:expr, $x9:expr, $($y:expr),+ $(,)?) => {
        or(
            or10($x0, $x1, $x2, $x3, $x4, $x5, $x6, $x7, $x8, $x9),
            or!($($y),+)
        )
    };
);

/// An XOR relation of variable arguments.
#[macro_export]
macro_rules! xor(
    ($x0:expr $(,)?) => {$x0};
    ($x0:expr, $x1:expr $(,)?) => {
        xor($x0, $x1)
    };
    ($x0:expr, $x1:expr, $x2:expr $(,)?) => {
        xor3($x0, $x1, $x2)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr $(,)?) => {
        xor4($x0, $x1, $x2, $x3)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr $(,)?) => {
        xor5($x0, $x1, $x2, $x3, $x4)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr, $x5:expr $(,)?) => {
        xor6($x0, $x1, $x2, $x3, $x4, $x5)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr, $x5:expr, $x6:expr $(,)?) => {
        xor7($x0, $x1, $x2, $x3, $x4, $x5, $x6)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr, $x5:expr, $x6:expr, $x7:expr $(,)?) => {
        xor8($x0, $x1, $x2, $x3, $x4, $x5, $x6, $x7)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr,
     $x5:expr, $x6:expr, $x7:expr, $x8:expr $(,)?) => {
        xor9($x0, $x1, $x2, $x3, $x4, $x5, $x6, $x7, $x8)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr,
     $x5:expr, $x6:expr, $x7:expr, $x8:expr, $x9:expr $(,)?) => {
        xor10($x0, $x1, $x2, $x3, $x4, $x5, $x6, $x7, $x8, $x9)
    };
    ($x0:expr, $($y:expr),+ $(,)?) => {
        or(
            and(not($x0), xor!($($y),+)),
            not(or(not($x0), or!($($y),+)))
        )
    };
);

/// An IMPLY chain of variable arguments.
#[macro_export]
macro_rules! imply(
    ($x0:expr $(,)?) => {$x0};
    ($x0:expr, $x1:expr $(,)?) => {
        imply($x0, $x1)
    };
    ($x0:expr, $x1:expr, $x2:expr $(,)?) => {
        imply3($x0, $x1, $x2)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr $(,)?) => {
        imply4($x0, $x1, $x2, $x3)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr $(,)?) => {
        imply5($x0, $x1, $x2, $x3, $x4)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr, $x5:expr $(,)?) => {
        imply6($x0, $x1, $x2, $x3, $x4, $x5)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr, $x5:expr, $x6:expr $(,)?) => {
        imply7($x0, $x1, $x2, $x3, $x4, $x5, $x6)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr, $x5:expr, $x6:expr, $x7:expr $(,)?) => {
        imply8($x0, $x1, $x2, $x3, $x4, $x5, $x6, $x7)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr,
     $x5:expr, $x6:expr, $x7:expr, $x8:expr $(,)?) => {
        imply9($x0, $x1, $x2, $x3, $x4, $x5, $x6, $x7, $x8)
    };
    ($x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr,
     $x5:expr, $x6:expr, $x7:expr, $x8:expr, $x9:expr $(,)?) => {
        imply10($x0, $x1, $x2, $x3, $x4, $x5, $x6, $x7, $x8, $x9)
    };
    ($x0:expr, $x1:expr, $($y:expr),+ $(,)?) => {
        and(imply($x0, $x1), imply!($x1, $($y),+))
    };
);

/// Counts the number of solutions of a variable argument boolean function.
///
/// Expands automatically to Path Semantical Logic when using tuples as arguments.
#[macro_export]
macro_rules! count(
    (&mut |$x0:ident $(,)?| $e:expr) => {
        count1(&mut |$x0| $e)
    };
    (&mut |$x0:ident, $x1:ident $(,)?| $e:expr) => {
        count2(&mut |$x0, $x1| $e)
    };
    (&mut |$x0:ident, $x1:ident, $x2:ident $(,)?| $e:expr) => {
        count3(&mut |$x0, $x1, $x2| $e)
    };
    (&mut |$x0:ident, $x1:ident, $x2:ident, $x3:ident $(,)?| $e:expr) => {
        count4(&mut |$x0, $x1, $x2, $x3| $e)
    };
    (&mut |$x0:ident, $x1:ident, $x2:ident, $x3:ident, $x4:ident $(,)?| $e:expr) => {
        count5(&mut |$x0, $x1, $x2, $x3, $x4| $e)
    };
    (&mut |$x0:ident, $x1:ident, $x2:ident, $x3:ident, $x4:ident, $x5:ident $(,)?| $e:expr) => {
        count6(&mut |$x0, $x1, $x2, $x3, $x4, $x5| $e)
    };
    (&mut |$x0:ident, $x1:ident, $x2:ident, $x3:ident, $x4:ident,
           $x5:ident, $x6:ident $(,)?| $e:expr) => {
        count7(&mut |$x0, $x1, $x2, $x3, $x4, $x5, $x6| $e)
    };
    (&mut |$x0:ident, $x1:ident, $x2:ident, $x3:ident,
           $x4:ident, $x5:ident, $x6:ident, $x7:ident $(,)?| $e:expr) => {
        count8(&mut |$x0, $x1, $x2, $x3, $x4, $x5, $x6, $x7| $e)
    };
    (&mut |$x0:ident, $x1:ident, $x2:ident, $x3:ident, $x4:ident,
           $x5:ident, $x6:ident, $x7:ident, $x8:ident| $e:expr) => {
        count9(&mut |$x0, $x1, $x2, $x3, $x4, $x5, $x6, $x7, $x8| $e)
    };
    (&mut |$x0:ident, $x1:ident, $x2:ident, $x3:ident, $x4:ident,
           $x5:ident, $x6:ident, $x7:ident, $x8:ident, $x9:ident $(,)?| $e:expr) => {
        count10(&mut |$x0, $x1, $x2, $x3, $x4, $x5, $x6, $x7, $x8, $x9| $e)
    };
    (&mut |$($x:ident),+ $(,)?| $e:expr) => {
        countn(tup_count!($($x),+), &mut |x| {
            tup_set!(x, ($($x),+));
            $e
        })
    };
    (&mut |($($x:ident),+ $(,)?), ($($y:ident),+ $(,)?)| $e:expr) => {
        path1_count!(&mut |($($x),+), ($($y),+)| $e)
    };
);

/// Helper macro for counting size of a tuple.
#[macro_export]
macro_rules! tup_count(
    () => {0};
    ($x0:ident $(, $y:ident)*) => {1 + tup_count!($($y),*)};
);

/// Helper macro for binding to a tuple pattern.
#[macro_export]
macro_rules! tup_set(
    ($f:ident, ($($x:ident),*)) => {tup_set!($f, 0, ($($x),*))};
    ($f:ident, $offset:expr, ($x0:ident)) => {
        let $x0 = $f[$offset];
    };
    ($f:ident, $offset:expr, ($x0:ident, $($y:ident),*)) => {
        let $x0 = $f[$offset];
        tup_set!($f, $offset+1, ($($y),*))
    };
);

/// Path Semantical Logic: Counts the number of solutions of a variable argument boolean function.
#[macro_export]
macro_rules! path1_count(
    (&mut |$x0:ident $(,)?| $e:expr) => {
        path1_count1(&mut |$x0| $e)
    };
    (&mut |$x0:ident, $x1:ident $(,)?| $e:expr) => {
        path1_count2(&mut |$x0, $x1| $e)
    };
    (&mut |($x0:ident, $x1:ident $(,)?), $x2:ident $(,)?| $e:expr) => {
        path1_count3(&mut |($x0, $x1), $x2| $e)
    };
    (&mut |($x0:ident, $x1:ident $(,)?), ($x2:ident, $x3:ident $(,)?)| $e:expr) => {
        path1_count4(&mut |($x0, $x1), ($x2, $x3)| $e)
    };
    (&mut |($x0:ident, $x1:ident, $x2:ident $(,)?), ($x3:ident, $x4:ident $(,)?)| $e:expr) => {
        path1_count5(&mut |($x0, $x1, $x2), ($x3, $x4)| $e)
    };
    (&mut |($x0:ident, $x1:ident, $x2:ident $(,)?), ($x3:ident, $x4:ident, $x5:ident $(,)?)| $e:expr) => {
        path1_count6(&mut |($x0, $x1, $x2), ($x3, $x4, $x5)| $e)
    };
    (&mut |($x0:ident, $x1:ident, $x2:ident, $x3:ident $(,)?),
           ($x4:ident, $x5:ident, $x6:ident $(,)?)| $e:expr) => {
        path1_count7(&mut |($x0, $x1, $x2, $x3), ($x4, $x5, $x6)| $e)
    };
    (&mut |($x0:ident, $x1:ident, $x2:ident, $x3:ident $(,)?),
           ($x4:ident, $x5:ident, $x6:ident, $x7:ident $(,)?)| $e:expr) => {
        path1_count8(&mut |($x0, $x1, $x2, $x3), ($x4, $x5, $x6, $x7)| $e)
    };
    (&mut |($x0:ident, $x1:ident, $x2:ident, $x3:ident, $x4:ident $(,)?),
           ($x5:ident, $x6:ident, $x7:ident, $x8:ident $(,)?)| $e:expr) => {
        path1_count9(&mut |($x0, $x1, $x2, $x3, $x4), ($x5, $x6, $x7, $x8)| $e)
    };
    (&mut |($x0:ident, $x1:ident, $x2:ident, $x3:ident, $x4:ident $(,)?),
           ($x5:ident, $x6:ident, $x7:ident, $x8:ident, $x9:ident $(,)?)| $e:expr) => {
        path1_count10(&mut |($x0, $x1, $x2, $x3, $x4), ($x5, $x6, $x7, $x8, $x9)| $e)
    };
    (&mut |($($x:ident),+ $(,)?), ($($y:ident),+ $(,)?)| $e:expr) => {
        path1_countnm(tup_count!($($x),+), tup_count!($($y),+), &mut |f, x| {
            tup_set!(f, ($($x),+));
            tup_set!(x, ($($y),+));
            $e
        })
    };
);

/// Returns `true` if proposition is correct, `false` otherwise.
///
/// Expands automatically to Path Semantical Logic when using tuples as arguments.
#[macro_export]
macro_rules! prove(
    (&mut |$x0:ident $(,)?| $e:expr) => {
        prove1(&mut |$x0| $e)
    };
    (&mut |$x0:ident, $x1:ident $(,)?| $e:expr) => {
        prove2(&mut |$x0, $x1| $e)
    };
    (&mut |$x0:ident, $x1:ident, $x2:ident $(,)?| $e:expr) => {
        prove3(&mut |$x0, $x1, $x2| $e)
    };
    (&mut |$x0:ident, $x1:ident, $x2:ident, $x3:ident $(,)?| $e:expr) => {
        prove4(&mut |$x0, $x1, $x2, $x3| $e)
    };
    (&mut |$x0:ident, $x1:ident, $x2:ident, $x3:ident, $x4:ident $(,)?| $e:expr) => {
        prove5(&mut |$x0, $x1, $x2, $x3, $x4| $e)
    };
    (&mut |$x0:ident, $x1:ident, $x2:ident, $x3:ident, $x4:ident, $x5:ident $(,)?| $e:expr) => {
        prove6(&mut |$x0, $x1, $x2, $x3, $x4, $x5| $e)
    };
    (&mut |$x0:ident, $x1:ident, $x2:ident, $x3:ident, $x4:ident,
           $x5:ident, $x6:ident $(,)?| $e:expr) => {
        prove7(&mut |$x0, $x1, $x2, $x3, $x4, $x5, $x6| $e)
    };
    (&mut |$x0:ident, $x1:ident, $x2:ident, $x3:ident,
           $x4:ident, $x5:ident, $x6:ident, $x7:ident $(,)?| $e:expr) => {
        prove8(&mut |$x0, $x1, $x2, $x3, $x4, $x5, $x6, $x7| $e)
    };
    (&mut |$x0:ident, $x1:ident, $x2:ident, $x3:ident, $x4:ident,
           $x5:ident, $x6:ident, $x7:ident, $x8:ident $(,)?| $e:expr) => {
        prove9(&mut |$x0, $x1, $x2, $x3, $x4, $x5, $x6, $x7, $x8| $e)
    };
    (&mut |$x0:ident, $x1:ident, $x2:ident, $x3:ident, $x4:ident,
           $x5:ident, $x6:ident, $x7:ident, $x8:ident, $x9:ident $(,)?| $e:expr) => {
        prove10(&mut |$x0, $x1, $x2, $x3, $x4, $x5, $x6, $x7, $x8, $x9| $e)
    };
    (&mut |$($x:ident),+ $(,)?| $e:expr) => {
        proven(tup_count!($($x),+), &mut |x| {
            tup_set!(x, ($($x),+));
            $e
        })
    };
    (&mut |($($x:ident),+ $(,)?), ($($y:ident),+ $(,)?)| $e:expr) => {
        path1_prove!(&mut |($($x),+), ($($y),+)| $e)
    };
);

/// Path Semantical Logic: Returns `true` if proposition is correct, `false` otherwise.
#[macro_export]
macro_rules! path1_prove(
    (&mut |$x0:ident $(,)?| $e:expr) => {
        path1_prove1(&mut |$x0| $e)
    };
    (&mut |$x0:ident, $x1:ident $(,)?| $e:expr) => {
        path1_prove2(&mut |$x0, $x1| $e)
    };
    (&mut |($x0:ident, $x1:ident $(,)?), $x2:ident $(,)?| $e:expr) => {
        path1_prove3(&mut |($x0, $x1), $x2| $e)
    };
    (&mut |($x0:ident, $x1:ident $(,)?), ($x2:ident, $x3:ident $(,)?)| $e:expr) => {
        path1_prove4(&mut |($x0, $x1), ($x2, $x3)| $e)
    };
    (&mut |($x0:ident, $x1:ident, $x2:ident $(,)?), ($x3:ident, $x4:ident $(,)?)| $e:expr) => {
        path1_prove5(&mut |($x0, $x1, $x2), ($x3, $x4)| $e)
    };
    (&mut |($x0:ident, $x1:ident, $x2:ident $(,)?), ($x3:ident, $x4:ident, $x5:ident $(,)?)| $e:expr) => {
        path1_prove6(&mut |($x0, $x1, $x2), ($x3, $x4, $x5)| $e)
    };
    (&mut |($x0:ident, $x1:ident, $x2:ident, $x3:ident $(,)?),
           ($x4:ident, $x5:ident, $x6:ident $(,)?)| $e:expr) => {
        path1_prove7(&mut |($x0, $x1, $x2, $x3), ($x4, $x5, $x6)| $e)
    };
    (&mut |($x0:ident, $x1:ident, $x2:ident, $x3:ident $(,)?),
           ($x4:ident, $x5:ident, $x6:ident, $x7:ident $(,)?)| $e:expr) => {
        path1_prove8(&mut |($x0, $x1, $x2, $x3), ($x4, $x5, $x6, $x7)| $e)
    };
    (&mut |($x0:ident, $x1:ident, $x2:ident, $x3:ident, $x4:ident $(,)?),
           ($x5:ident, $x6:ident, $x7:ident, $x8:ident $(,)?)| $e:expr) => {
        path1_prove9(&mut |($x0, $x1, $x2, $x3, $x4), ($x5, $x6, $x7, $x8)| $e)
    };
    (&mut |($x0:ident, $x1:ident, $x2:ident, $x3:ident, $x4:ident $(,)?),
           ($x5:ident, $x6:ident, $x7:ident, $x8:ident, $x9:ident $(,)?)| $e:expr) => {
        path1_prove10(&mut |($x0, $x1, $x2, $x3, $x4), ($x5, $x6, $x7, $x8, $x9)| $e)
    };
    (&mut |($($x:ident),+ $(,)?), ($($y:ident),+ $(,)?)| $e:expr) => {
        path1_provenm(tup_count!($($x),+), tup_count!($($y),+), &mut |f, x| {
            tup_set!(f, ($($x),+));
            tup_set!(x, ($($y),+));
            $e
        })
    };
);

/// Path Semantical Logic: A contractible "family of types".
///
/// All propositions are either `true` or all propositions are `false`.
#[macro_export]
macro_rules! contr(
    ($($x:expr),*) => {
        xor(and!($($x),*), and!($(not($x)),*))
    }
);

/// The False proposition.
/// Used to alternate higher than 6 arguments, set to `0`.
pub const F: u64 = 0b00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000;
/// 0xaaaa_aaaa_aaaa_aaaa
pub const P0: u64 = 0b10101010_10101010_10101010_10101010_10101010_10101010_10101010_10101010;
/// 0xcccc_cccc_cccc_cccc
pub const P1: u64 = 0b11001100_11001100_11001100_11001100_11001100_11001100_11001100_11001100;
/// 0xf0f0_f0f0_f0f0_f0f0
pub const P2: u64 = 0b11110000_11110000_11110000_11110000_11110000_11110000_11110000_11110000;
/// 0xff00_ff00_ff00_ff00
pub const P3: u64 = 0b11111111_00000000_11111111_00000000_11111111_00000000_11111111_00000000;
/// 0xffff_0000_ffff_0000
pub const P4: u64 = 0b11111111_11111111_00000000_00000000_11111111_11111111_00000000_00000000;
/// 0xffff_ffff_0000_0000
pub const P5: u64 = 0b11111111_11111111_11111111_11111111_00000000_00000000_00000000_00000000;
/// The True proposition.
/// Used to alternate higher than 6 arguments, set to `1`.
pub const T: u64 = 0b11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111;

/// Implemented by observables.
pub trait Observable {
    /// Gets the maximum energy level of observable.
    fn max_energy() -> Self;
    /// Gets the minimum energy level of two observables.
    fn min_energy(self, other: Self) -> Self;
}

impl Observable for bool {
    fn max_energy() -> bool {true}
    fn min_energy(self, other: bool) -> bool {self && other}
}

impl Observable for u32 {
    fn max_energy() -> u32 {std::u32::MAX}
    fn min_energy(self, other: u32) -> u32 {self.min(other)}
}

/// Prepares a qubit using a proposition as seed.
pub fn qubit(a: u64) -> u64 {
    use rand::{Rng, SeedableRng};
    use rand::rngs::StdRng;
    let r = unsafe {&*current::Current::<u64>::new()};
    let mut rng = StdRng::seed_from_u64(a ^ *r);
    rng.gen()
}

/// Amplify a "wavefunction" of a proposition using its qubit transform.
pub fn amplify(n: u32, mut a: u64) -> u64 {
    for _ in 0..n {
        a |= qubit(a);
    }
    a
}

/// Path semantical quality `a ~~ b`.
pub fn qual(a: u64, b: u64) -> u64 {
    and(eq(a, b), if a == b {qubit(a)} else {T})
}

/// Assumes the path semantical core axiom.
pub fn ps_core(a: u64, b: u64, c: u64, d: u64) -> u64 {
    imply(and!(qual(a, b), imply(a, c), imply(b, d)), qual(c, d))
}

/// Measures result repeatedly.
pub fn measure<O: Observable>(n: u32, mut fun: impl FnMut() -> O) -> O {
    let mut b = O::max_energy();
    for _ in 0..n {
        b = b.min_energy(fun());
    }
    b
}

fn call(mut fun: impl FnMut() -> u64) -> u64 {
    let mut r = rand::random::<u64>();
    let guard = current::CurrentGuard::new(&mut r);
    let res = fun();
    drop(guard);
    res
}

/// Counts the number of solutions of a 1-argument boolean function.
pub fn count1<F: FnMut(u64) -> u64>(f: &mut F) -> u32 {
    call(|| ((f)(P0) & 0x3)).count_ones()
}
/// Counts the number of solutions of a 2-argument boolean function.
pub fn count2<F: FnMut(u64, u64) -> u64>(f: &mut F) -> u32 {
    call(|| ((f)(P0, P1) & 0xf)).count_ones()
}
/// Counts the number of solutions of a 3-argument boolean function.
pub fn count3<F: FnMut(u64, u64, u64) -> u64>(f: &mut F) -> u32 {
    call(|| ((f)(P0, P1, P2) & 0xff)).count_ones()
}
/// Counts the number of solutions of a 4-argument boolean function.
pub fn count4<F: FnMut(u64, u64, u64, u64) -> u64>(f: &mut F) -> u32 {
    call(|| ((f)(P0, P1, P2, P3) & 0xffff)).count_ones()
}
/// Counts the number of solutions of a 5-argument boolean function.
pub fn count5<F: FnMut(u64, u64, u64, u64, u64) -> u64>(f: &mut F) -> u32 {
    call(|| ((f)(P0, P1, P2, P3, P4) & 0xffff_ffff)).count_ones()
}
/// Counts the number of solutions of a 6-argument boolean function.
pub fn count6<F: FnMut(u64, u64, u64, u64, u64, u64) -> u64>(f: &mut F) -> u32 {
    call(|| (f)(P0, P1, P2, P3, P4, P5)).count_ones()
}
/// Counts the number of solutions of a 7-argument boolean function.
pub fn count7<F: FnMut(u64, u64, u64, u64, u64, u64, u64) -> u64>(f: &mut F) -> u32 {
    call(|| (f)(P0, P1, P2, P3, P4, P5, F)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, T)).count_ones()
}
/// Counts the number of solutions of an 8-argument boolean function.
pub fn count8<F: FnMut(u64, u64, u64, u64, u64, u64, u64, u64) -> u64>(f: &mut F) -> u32 {
    call(|| (f)(P0, P1, P2, P3, P4, P5, F, F)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, F, T)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, T, F)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, T, T)).count_ones()
}
/// Counts the number of solutions of a 9-argument boolean function.
pub fn count9<F: FnMut(u64, u64, u64, u64, u64, u64, u64, u64, u64) -> u64>(f: &mut F) -> u32 {
    call(|| (f)(P0, P1, P2, P3, P4, P5, F, F, F)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, F, F, T)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, F, T, F)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, F, T, T)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, T, F, F)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, T, F, T)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, T, T, F)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, T, T, T)).count_ones()
}
/// Counts the number of solutions of a 10-argument boolean function.
pub fn count10<F: FnMut(u64, u64, u64, u64, u64, u64, u64, u64, u64, u64) -> u64>(f: &mut F) -> u32 {
    call(|| (f)(P0, P1, P2, P3, P4, P5, F, F, F, F)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, F, F, F, T)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, F, F, T, F)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, F, F, T, T)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, F, T, F, F)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, F, T, F, T)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, F, T, T, F)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, F, T, T, T)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, T, F, F, F)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, T, F, F, T)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, T, F, T, F)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, T, F, T, T)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, T, T, F, F)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, T, T, F, T)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, T, T, T, F)).count_ones() +
    call(|| (f)(P0, P1, P2, P3, P4, P5, T, T, T, T)).count_ones()
}
/// Counts the number of solutions of an n-argument boolean function.
pub fn countn(n: usize, fun: &mut dyn FnMut(&[u64]) -> u64) -> u64 {
    match n {
        0 => call(|| fun(&[])).count_ones() as u64,
        1 => count1(&mut |a| fun(&[a])) as u64,
        2 => count2(&mut |a, b| fun(&[a, b])) as u64,
        3 => count3(&mut |a, b, c| fun(&[a, b, c])) as u64,
        4 => count4(&mut |a, b, c, d| fun(&[a, b, c, d])) as u64,
        5 => count5(&mut |a, b, c, d, e| fun(&[a, b, c, d, e])) as u64,
        6 => count6(&mut |a, b, c, d, e, f| fun(&[a, b, c, d, e, f])) as u64,
        7 => count7(&mut |a, b, c, d, e, f, g| fun(&[a, b, c, d, e, f, g])) as u64,
        8 => count8(&mut |a, b, c, d, e, f, g, h| fun(&[a, b, c, d, e, f, g, h])) as u64,
        9 => count9(&mut |a, b, c, d, e, f, g, h, i| fun(&[a, b, c, d, e, f, g, h, i])) as u64,
        10 => count10(&mut |a, b, c, d, e, f, g, h, i, j| fun(&[a, b, c, d, e, f, g, h, i, j])) as u64,
        _ => {
            if n >= 19 {
                let ref mut args = vec![0; n];
                let mut sum = 0;
                for i in 0..512 {
                    args[0] = if (i & 0b1) == 0b1 {T} else {F};
                    args[1] = if (i & 0b10) == 0b10 {T} else {F};
                    args[2] = if (i & 0b100) == 0b100 {T} else {F};
                    args[3] = if (i & 0b1000) == 0b1000 {T} else {F};
                    args[4] = if (i & 0b10000) == 0b10000 {T} else {F};
                    args[5] = if (i & 0b100000) == 0b100000 {T} else {F};
                    args[6] = if (i & 0b1000000) == 0b1000000 {T} else {F};
                    args[7] = if (i & 0b10000000) == 0b10000000 {T} else {F};
                    args[8] = if (i & 0b100000000) == 0b100000000 {T} else {F};
                    sum += countn(n-9, &mut |vs: &[u64]| {
                        for i in 0..n-9 {args[i+9] = vs[i]}
                        call(|| fun(&args))
                    });
                }
                sum
            } else {
                let ref mut args = vec![0; n];
                let mut sum = 0;
                for i in 0..32 {
                    args[0] = if (i & 0b1) == 0b1 {T} else {F};
                    args[1] = if (i & 0b10) == 0b10 {T} else {F};
                    args[2] = if (i & 0b100) == 0b100 {T} else {F};
                    args[3] = if (i & 0b1000) == 0b1000 {T} else {F};
                    args[4] = if (i & 0b10000) == 0b10000 {T} else {F};
                    sum += countn(n-5, &mut |vs: &[u64]| {
                        for i in 0..n-5 {args[i+5] = vs[i]}
                        call(|| fun(&args))
                    });
                }
                sum
            }
        }
    }
}

/// Path Semantical Logic: Counts the number of solutions of a 1-argument boolean function,
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
///
/// For 1-argument functions this is the same as normal counting of solutions.
pub fn path1_count1<F: FnMut(u64) -> u64>(f: &mut F) -> u32 {count1(f)}
/// Path Semantical Logic: Counts the number of solutions of a 2-argument boolean function,
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
///
/// For 2-argument functions this is the same as normal counting of solutions.
pub fn path1_count2<F: FnMut(u64, u64) -> u64>(f: &mut F) -> u32 {count2(f)}
/// Path Semantical Logic: Counts the number of solutions of a 3-argument boolean function,
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
///
/// For 3-argument functions this is the same as normal counting of solutions.
pub fn path1_count3<F: FnMut((u64, u64), u64) -> u64>(f: &mut F) -> u32 {
    ((f)((0b00001111,
          0b00110011),
          0b01010101,
    ) & 0b11111111).count_ones()
}
/// Path Semantical Logic: Counts the number of solutions of a 4-argument boolean function,
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
pub fn path1_count4<F: FnMut((u64, u64), (u64, u64)) -> u64>(f: &mut F) -> u32 {
    ((f)((0b00000011111111,
          0b00111100001111),
         (0b01001100110011,
          0b01010101010101)
     ) & 0b11111111111111).count_ones()
}
/// Path Semantical Logic: Counts the number of solutions of a 5-argument boolean function,
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
pub fn path1_count5<F: FnMut((u64, u64, u64), (u64, u64)) -> u64>(f: &mut F) -> u32 {
    ((f)((0b000000000011111111111111,
          0b000011111100000011111111,
          0b001100111100111100001111),
         (0b010101001101001100110011,
          0b010101010101010101010101))
        & 0b11111_11111_11111_11111_1111).count_ones()
}
/// Path Semantical Logic: Counts the number of solutions of a 6-argument boolean function,
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
pub fn path1_count6<F: FnMut((u64, u64, u64), (u64, u64, u64)) -> u64>(f: &mut F) -> u32 {
    ((f)((0b0000000000000011111111111111111111111111,
          0b0000111111111100000000001111111111111111,
          0b0011001111111100111111110000000011111111),
         (0b0101010000111101000011110000111100001111,
          0b0101010011001101001100110011001100110011,
          0b0101010101010101010101010101010101010101))
         & 0b11111_11111_11111_11111_11111_11111_11111_11111).count_ones()
}
/// Path Semantical Logic: Counts the number of solutions of a 7-argument boolean function,
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
pub fn path1_count7<F: FnMut((u64, u64, u64, u64), (u64, u64, u64)) -> u64>(f: &mut F) -> u32 {
    ((f)((0b00000000000000000000001111111111111111111111111111111111111111,
          0b00000000111111111111110000000000000011111111111111111111111111,
          0b00001111000011111111110000111111111100000000001111111111111111,
          0b00110011001100111111110011001111111100111111110000000011111111),
         (0b01010101010101000011110101010000111101000011110000111100001111,
          0b01010101010101001100110101010011001101001100110011001100110011,
          0b01010101010101010101010101010101010101010101010101010101010101)
    ) & 0b11111_11111_11111_11111_11111_11111_11111_11111_11111_11111_11111_11111_11).count_ones()
}
/// Path Semantical Logic: Counts the number of solutions of a 8-argument boolean function,
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
pub fn path1_count8<F: FnMut((u64, u64, u64, u64), (u64, u64, u64, u64)) -> u64>(f: &mut F) -> u32 {
    ((f)((0b0000000000000000000000000000001111111111111111111111111111111111,
          0b0000000011111111111111111111110000000000000000000000111111111111,
          0b0000111100001111111111111111110000111111111111111111000000000000,
          0b0011001100110011111111111111110011001111111111111111001111111111),
         (0b0101010101010100000000111111110101010000000011111111010000000011,
          0b0101010101010100001111000011110101010000111100001111010000111100,
          0b0101010101010100110011001100110101010011001100110011010011001100,
          0b0101010101010101010101010101010101010101010101010101010101010101))).count_ones() +
    ((f)((0b11111111111111111111111111111111111111,
          0b11111111111111111111111111111111111111,
          0b00000011111111111111111111111111111111,
          0b11111100000000000000001111111111111111),
         (0b11111100000000111111110000000011111111,
          0b00111100001111000011110000111100001111,
          0b11001100110011001100110011001100110011,
          0b01010101010101010101010101010101010101))
       & 0b11111_11111_11111_11111_11111_11111_11111_111).count_ones()
}
/// Path Semantical Logic: Counts the number of solutions of a 9-argument boolean function,
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
pub fn path1_count9<F: FnMut((u64, u64, u64, u64, u64), (u64, u64, u64, u64)) -> u64>(f: &mut F) -> u32 {
    ((f)((0b0000000000000000000000000000000000000000000000111111111111111111,
          0b0000000000000000111111111111111111111111111111000000000000000000,
          0b0000000011111111000000001111111111111111111111000000001111111111,
          0b0000111100001111000011110000111111111111111111000011110000111111,
          0b0011001100110011001100110011001111111111111111001100110011001111),
         (0b0101010101010101010101010101010000000011111111010101010101010000,
          0b0101010101010101010101010101010000111100001111010101010101010000,
          0b0101010101010101010101010101010011001100110011010101010101010011,
          0b0101010101010101010101010101010101010101010101010101010101010101))).count_ones() +
    ((f)((0b1111111111111111111111111111111111111111111111111111111111111111,
          0b0000000000001111111111111111111111111111111111111111111111111111,
          0b1111111111110000000000000000000000111111111111111111111111111111,
          0b1111111111110000111111111111111111000000000000000000111111111111,
          0b1111111111110011001111111111111111001111111111111111000000000000),
         (0b0000111111110101010000000011111111010000000011111111000000001111,
          0b1111000011110101010000111100001111010000111100001111000011110000,
          0b0011001100110101010011001100110011010011001100110011001100110011,
          0b0101010101010101010101010101010101010101010101010101010101010101))).count_ones() +
    ((f)((0b11111111111111111111,
          0b11111111111111111111,
          0b11111111111111111111,
          0b11111111111111111111,
          0b00001111111111111111),
         (0b11110000000011111111,
          0b11110000111100001111,
          0b00110011001100110011,
          0b01010101010101010101))
        & 0b11111_11111_11111_11111).count_ones()
}
/// Path Semantical Logic: Counts the number of solutions of a 10-argument boolean function,
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
pub fn path1_count10<F: FnMut((u64, u64, u64, u64, u64), (u64, u64, u64, u64, u64)) -> u64>(f: &mut F) -> u32 {
    ((f)((0b0000000000000000000000000000000000000000000000000000000000000011,
          0b0000000000000000111111111111111111111111111111111111111111111100,
          0b0000000011111111000000001111111111111111111111111111111111111100,
          0b0000111100001111000011110000111111111111111111111111111111111100,
          0b0011001100110011001100110011001111111111111111111111111111111100),
         (0b0101010101010101010101010101010000000000000000111111111111111101,
          0b0101010101010101010101010101010000000011111111000000001111111101,
          0b0101010101010101010101010101010000111100001111000011110000111101,
          0b0101010101010101010101010101010011001100110011001100110011001101,
          0b0101010101010101010101010101010101010101010101010101010101010101))).count_ones() +
    ((f)((0b1111111111111111111111111111111111111111111111111111111111111111,
          0b0000000000000000000000000000000000000000000011111111111111111111,
          0b0000001111111111111111111111111111111111111100000000000000000000,
          0b0011110000111111111111111111111111111111111100001111111111111111,
          0b1100110011001111111111111111111111111111111100110011111111111111),
         (0b0101010101010000000000000000111111111111111101010100000000000000,
          0b0101010101010000000011111111000000001111111101010100000000111111,
          0b0101010101010000111100001111000011110000111101010100001111000011,
          0b0101010101010011001100110011001100110011001101010100110011001100,
          0b0101010101010101010101010101010101010101010101010101010101010101))).count_ones() +
    ((f)((0b1111111111111111111111111111111111111111111111111111111111111111,
          0b1111111111111111111111111111111111111111111111111111111111111111,
          0b0000000000000000001111111111111111111111111111111111111111111111,
          0b1111111111111111110000000000000000000000000000000000111111111111,
          0b1111111111111111110011111111111111111111111111111111000000000000),
         (0b0011111111111111110100000000000000001111111111111111000000000000,
          0b1100000000111111110100000000111111110000000011111111000000001111,
          0b1100001111000011110100001111000011110000111100001111000011110000,
          0b1100110011001100110100110011001100110011001100110011001100110011,
          0b0101010101010101010101010101010101010101010101010101010101010101))).count_ones() +
    ((f)((0b1111111111111111111111111111111111111111111111111111,
          0b1111111111111111111111111111111111111111111111111111,
          0b1111111111111111111111111111111111111111111111111111,
          0b1111111111111111111111111111111111111111111111111111,
          0b0000000000000000000011111111111111111111111111111111),
         (0b0000111111111111111100000000000000001111111111111111,
          0b1111000000001111111100000000111111110000000011111111,
          0b1111000011110000111100001111000011110000111100001111,
          0b0011001100110011001100110011001100110011001100110011,
          0b0101010101010101010101010101010101010101010101010101))
        & 0b11111_11111_11111_11111_11111_11111_11111_11111_11111_11111_11).count_ones()
}
/// Path Semantical Logic: Counts the number of solutions of a n-argument boolean function,
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
pub fn path1_countn(n: usize, fun: &mut dyn FnMut(&[u64], &[u64]) -> u64) -> u64 {
    match n {
        0 => call(|| fun(&[], &[])).count_ones() as u64,
        1 => path1_count1(&mut |a| fun(&[a], &[])) as u64,
        2 => path1_count2(&mut |a, b| fun(&[a], &[b])) as u64,
        3 => path1_count3(&mut |(a, b), c| fun(&[a, b], &[c])) as u64,
        4 => path1_count4(&mut |(a, b), (c, d)| fun(&[a, b], &[c, d])) as u64,
        5 => path1_count5(&mut |(a, b, c), (d, e)| fun(&[a, b, c], &[d, e])) as u64,
        6 => path1_count6(&mut |(a, b, c), (d, e, f)| fun(&[a, b, c], &[d, e, f])) as u64,
        7 => path1_count7(&mut |(a, b, c, d), (e, f, g)| fun(&[a, b, c, d], &[e, f, g])) as u64,
        8 => path1_count8(&mut |(a, b, c, d), (e, f, g, h)| fun(&[a, b, c, d], &[e, f, g, h])) as u64,
        9 => path1_count9(&mut |(a, b, c, d, e), (f, g, h, i)| fun(&[a, b, c, d, e], &[f, g, h, i])) as u64,
        10 => path1_count10(&mut |(a, b, c, d, e), (f, g, h, i, j)| fun(&[a, b, c, d, e], &[f, g, h, i, j])) as u64,
        n => {
            let x = n / 2;
            let f = n - x;
            path1_countnm(f, x, fun)
        }
    }
}

/// Path Semantical Logic: Counts the number of solutions of a n+m-argument boolean function,
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
pub fn path1_countnm(f: usize, x: usize, fun: &mut dyn FnMut(&[u64], &[u64]) -> u64) -> u64 {
    // Reuse `countn` with a few redundant edge cases.
    // The redundant edge cases are subtracted to get correct count.
    //
    // This algorithm was derived by analyzing the time complexity formula:
    // https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/complexity-of-path-semantical-logic.pdf
    let mut xs = vec![0; x];
    // Enumerate all cases when `xs` are zero.
    let all_xs_zero = countn(f, &mut |fs| fun(fs, &*xs));
    // Enumerate all cases when `xs` are ones.
    for x in &mut xs {*x = T};
    let all_xs_one = countn(f, &mut |fs| fun(fs, &*xs));
    // Set `xs` to first and last case.
    for x in &mut xs {*x = 0b01};
    // Enumerate all cases when `fs` are ones.
    let mut fs = vec![T; f];
    let mut all_fs_one = countn(x, &mut |xs| fun(&*fs, xs));
    // Subtract first and last case.
    all_fs_one -= call(|| (fun(&*fs, &*xs) & 0b11)).count_ones() as u64;
    let mut sum_fs_zero = 0;
    // Set one zero in `fs` by turn.
    for i in 0..f {
        fs[i] = F;
        // Enumerate all cases when there is one zero in `fs`.
        sum_fs_zero += countn(x, &mut |xs| fun(&*fs, xs));
        // Subtract first and last case.
        sum_fs_zero -= call(|| (fun(&*fs, &*xs) & 0b11)).count_ones() as u64;
        fs[i] = T;
    }
    all_xs_zero + all_xs_one + all_fs_one + sum_fs_zero
}

/// Returns `true` if proposition is correct, `false` otherwise.
pub fn prove1<F: FnMut(u64) -> u64>(f: &mut F) -> bool {count1(f) == 2}
/// Returns `true` if proposition is correct, `false` otherwise.
pub fn prove2<F: FnMut(u64, u64) -> u64>(f: &mut F) -> bool {count2(f) == 4}
/// Returns `true` if proposition is correct, `false` otherwise.
pub fn prove3<F: FnMut(u64, u64, u64) -> u64>(f: &mut F) -> bool {count3(f) == 8}
/// Returns `true` if proposition is correct, `false` otherwise.
pub fn prove4<F: FnMut(u64, u64, u64, u64) -> u64>(f: &mut F) -> bool {count4(f) == 16}
/// Returns `true` if proposition is correct, `false` otherwise.
pub fn prove5<F: FnMut(u64, u64, u64, u64, u64) -> u64>(f: &mut F) -> bool {count5(f) == 32}
/// Returns `true` if proposition is correct, `false` otherwise.
pub fn prove6<F: FnMut(u64, u64, u64, u64, u64, u64) -> u64>(f: &mut F) -> bool {count6(f) == 64}
/// Returns `true` if proposition is correct, `false` otherwise.
pub fn prove7<F: FnMut(u64, u64, u64, u64, u64, u64, u64) -> u64>(f: &mut F) -> bool {count7(f) == 128}
/// Returns `true` if proposition is correct, `false` otherwise.
pub fn prove8<F: FnMut(u64, u64, u64, u64, u64, u64, u64, u64) -> u64>(f: &mut F) -> bool {
    count8(f) == 256
}
/// Returns `true` if proposition is correct, `false` otherwise.
pub fn prove9<F: FnMut(u64, u64, u64, u64, u64, u64, u64, u64, u64) -> u64>(f: &mut F) -> bool {
    count9(f) == 512
}
/// Returns `true` if proposition is correct, `false` otherwise.
pub fn prove10<F: FnMut(u64, u64, u64, u64, u64, u64, u64, u64, u64, u64) -> u64>(f: &mut F) -> bool {
    count10(f) == 1024
}
/// Returns `true` if proposition is correct, `false` otherwise.
pub fn proven<F: FnMut(&[u64]) -> u64>(n: usize, f: &mut F) -> bool {
    countn(n, f) == 1 << n
}

/// Path Semantical Logic: Returns `true` if proposition is correct, `false` otherwise.
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
///
/// For 1-argument functions this is the same as normal theorem proving.
pub fn path1_prove1<F: FnMut(u64) -> u64>(f: &mut F) -> bool {prove1(f)}
/// Path Semantical Logic: Returns `true` if proposition is correct, `false` otherwise.
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
///
/// For 2-argument functions this is the same as normal theorem proving.
pub fn path1_prove2<F: FnMut(u64, u64) -> u64>(f: &mut F) -> bool {prove2(f)}
/// Path Semantical Logic: Returns `true` if proposition is correct, `false` otherwise.
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
pub fn path1_prove3<F: FnMut((u64, u64), u64) -> u64>(f: &mut F) -> bool {path1_count3(f) == 8}
/// Path Semantical Logic: Returns `true` if proposition is correct, `false` otherwise.
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
pub fn path1_prove4<F: FnMut((u64, u64), (u64, u64)) -> u64>(f: &mut F) -> bool {
    path1_count4(f) == 14
}
/// Path Semantical Logic: Returns `true` if proposition is correct, `false` otherwise.
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
pub fn path1_prove5<F: FnMut((u64, u64, u64), (u64, u64)) -> u64>(f: &mut F) -> bool {
    path1_count5(f) == 24
}
/// Path Semantical Logic: Returns `true` if proposition is correct, `false` otherwise.
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
pub fn path1_prove6<F: FnMut((u64, u64, u64), (u64, u64, u64)) -> u64>(f: &mut F) -> bool {
    path1_count6(f) == 40
}
/// Path Semantical Logic: Returns `true` if proposition is correct, `false` otherwise.
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
pub fn path1_prove7<F: FnMut((u64, u64, u64, u64), (u64, u64, u64)) -> u64>(f: &mut F) -> bool {
    path1_count7(f) == 62
}
/// Path Semantical Logic: Returns `true` if proposition is correct, `false` otherwise.
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
pub fn path1_prove8<F: FnMut((u64, u64, u64, u64), (u64, u64, u64, u64)) -> u64>(f: &mut F) -> bool {
    path1_count8(f) == 102
}
/// Path Semantical Logic: Returns `true` if proposition is correct, `false` otherwise.
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
pub fn path1_prove9<F: FnMut((u64, u64, u64, u64, u64), (u64, u64, u64, u64)) -> u64>(f: &mut F) -> bool {
    path1_count9(f) == 148
}
/// Path Semantical Logic: Returns `true` if proposition is correct, `false` otherwise.
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
pub fn path1_prove10<F: FnMut((u64, u64, u64, u64, u64), (u64, u64, u64, u64, u64)) -> u64>(f: &mut F) -> bool {
    path1_count10(f) == 244
}
/// Path Semantical Logic: Returns `true` if proposition is correct, `false` otherwise.
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
pub fn path1_proven<F: FnMut(&[u64], &[u64]) -> u64>(n: usize, fun: &mut F) -> bool {
    let x = n / 2;
    let f = n - x;
    path1_countn(n, fun) == path1_lennm(f, x)
}

/// Path Semantical Logic: Computes number of cases.
///
/// For proof of formula,
/// see https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/complexity-of-path-semantical-logic.pdf
pub fn path1_lennm(f: usize, x: usize) -> u64 {
    let f = f as u32;
    let x = x as u32;
    2_u64.pow(1 + f) + (1 + f as u64) * (2_u64.pow(x) - 2)
}

/// Path Semantical Logic: Returns `true` if proposition is correct, `false` otherwise.
///
/// For more information, see the section "Path Semantical Logic" at the top level documentation.
pub fn path1_provenm<F: FnMut(&[u64], &[u64]) -> u64>(f: usize, x: usize, fun: &mut F) -> bool {
    path1_countnm(f, x, fun) == path1_lennm(f, x)
}

/// Returns `T` if `a` is `true`, `F` otherwise.
/// In logical terminology this corresponds to a proposition.
pub fn prop(a: bool) -> u64 {if a {T} else {F}}

/// Ignores argument, always returning `false`.
pub fn false_1(_: u64) -> u64 {0}
/// If input is `true`, returns `false` and vice versa.
pub fn not(a: u64) -> u64 {!a}
/// Returns argument.
pub fn id(a: u64) -> u64 {a}
/// Ignores argument, always returning `true`.
pub fn true_1(_: u64) -> u64 {T}

/// Ignores both arguments, returning `false` for all inputs.
pub fn false_2(_: u64, _: u64) -> u64 {0}
/// Returns `true` if all arguments are `true`.
pub fn and(a: u64, b: u64) -> u64 {a & b}
/// Returns `true` if at least one argument is `true`.
pub fn or(a: u64, b: u64) -> u64 {a | b}
/// Returns `true` if only one argument is `true`.
pub fn xor(a: u64, b: u64) -> u64 {a ^ b}
/// Returns `true` if arguments are equal.
pub fn eq(a: u64, b: u64) -> u64 {!(a ^ b)}
/// First argument implies the second.
pub fn imply(a: u64, b: u64) -> u64 {!a | b}
/// Ignores both arguments, returning `true` for all inputs.
pub fn true_2(_: u64, _: u64) -> u64 {T}

/// Ignores all 3 arguments, returning `false` for all inputs.
pub fn false_3(_: u64, _: u64, _: u64) -> u64 {0}
/// Ignores all 4 arguments, returning `false` for all inputs.
pub fn false_4(_: u64, _: u64, _: u64, _: u64) -> u64 {0}
/// Ignores all 5 arguments, returning `false` for all inputs.
pub fn false_5(_: u64, _: u64, _: u64, _: u64, _: u64) -> u64 {0}
/// Ignores all 6 arguments, returning `false` for all inputs.
pub fn false_6(_: u64, _: u64, _: u64, _: u64, _: u64, _: u64) -> u64 {0}
/// Ignores all 7 arguments, returning `false` for all inputs.
pub fn false_7(_: u64, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64) -> u64 {0}
/// Ignores all 8 arguments, returning `false` for all inputs.
pub fn false_8(_: u64, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64) -> u64 {0}
/// Ignores all 9 arguments, returning `false` for all inputs.
pub fn false_9(_: u64, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64) -> u64 {0}
/// Ignores all 10 arguments, returning `false` for all inputs.
pub fn false_10(
    _: u64, _: u64, _: u64, _: u64, _: u64,
    _: u64, _: u64, _: u64, _: u64, _: u64
) -> u64 {0}

/// Ignores all 3 arguments, returning `true` for all inputs.
pub fn true_3(_: u64, _: u64, _: u64) -> u64 {T}
/// Ignores all 4 arguments, returning `true` for all inputs.
pub fn true_4(_: u64, _: u64, _: u64, _: u64) -> u64 {T}
/// Ignores all 5 arguments, returning `true` for all inputs.
pub fn true_5(_: u64, _: u64, _: u64, _: u64, _: u64) -> u64 {T}
/// Ignores all 6 arguments, returning `true` for all inputs.
pub fn true_6(_: u64, _: u64, _: u64, _: u64, _: u64, _: u64) -> u64 {T}
/// Ignores all 7 arguments, returning `true` for all inputs.
pub fn true_7(_: u64, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64) -> u64 {T}
/// Ignores all 8 arguments, returning `true` for all inputs.
pub fn true_8(_: u64, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64) -> u64 {T}
/// Ignores all 9 arguments, returning `true` for all inputs.
pub fn true_9(_: u64, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64) -> u64 {T}
/// Ignores all 10 arguments, returning `true` for all inputs.
pub fn true_10(
    _: u64, _: u64, _: u64, _: u64, _: u64,
    _: u64, _: u64, _: u64, _: u64, _: u64
) -> u64 {T}

/// An AND relation of 3 argument.
pub fn and3(a: u64, b: u64, c: u64) -> u64 {and(and(a, b), c)}
/// An AND relation of 4 arguments.
pub fn and4(a: u64, b: u64, c: u64, d: u64) -> u64 {and(and(a, b), and(c, d))}
/// An AND relation of 5 arguments.
pub fn and5(a: u64, b: u64, c: u64, d: u64, e: u64) -> u64 {and(and(a, b), and3(c, d, e))}
/// An AND relation of 6 arguments.
pub fn and6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64) -> u64 {
    and(and3(a, b, c), and3(d, e, f))
}
/// An AND relation of 7 arguments.
pub fn and7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64) -> u64 {
    and(and4(a, b, c, d), and3(e, f, g))
}
/// An AND relation of 8 arguments.
pub fn and8(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64) -> u64 {
    and(and4(a, b, c, d), and4(e, f, g, h))
}
/// An AND relation of 9 arguments.
pub fn and9(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, i: u64) -> u64 {
    and(and5(a, b, c, d, e), and4(f, g, h, i))
}
/// An AND relation of 10 arguments.
pub fn and10(
    a: u64, b: u64, c: u64, d: u64, e: u64,
    f: u64, g: u64, h: u64, i: u64, j: u64
) -> u64 {
    and(and5(a, b, c, d, e), and5(f, g, h, i, j))
}
/// An AND relation of variable number of arguments.
pub fn andn(vs: &[u64]) -> u64 {
    match vs.len() {
        0 => T,
        1 => vs[0],
        2 => and(vs[0], vs[1]),
        3 => and3(vs[0], vs[1], vs[2]),
        4 => and4(vs[0], vs[1], vs[2], vs[3]),
        5 => and5(vs[0], vs[1], vs[2], vs[3], vs[4]),
        6 => and6(vs[0], vs[1], vs[2], vs[3], vs[4], vs[5]),
        7 => and7(vs[0], vs[1], vs[2], vs[3], vs[4], vs[5], vs[6]),
        8 => and8(vs[0], vs[1], vs[2], vs[3], vs[4], vs[5], vs[6], vs[7]),
        9 => and9(vs[0], vs[1], vs[2], vs[3], vs[4], vs[5], vs[6], vs[7], vs[8]),
        10 => and10(vs[0], vs[1], vs[2], vs[3], vs[4], vs[5], vs[6], vs[7], vs[8], vs[9]),
        _ => and(andn(&vs[..10]), andn(&vs[10..]))
    }
}

/// An OR relation of 3 arguments.
pub fn or3(a: u64, b: u64, c: u64) -> u64 {or(or(a, b), c)}
/// An OR relation of 4 arguments.
pub fn or4(a: u64, b: u64, c: u64, d: u64) -> u64 {or(or(a, b), or(c, d))}
/// An OR relation of 5 arguments.
pub fn or5(a: u64, b: u64, c: u64, d: u64, e: u64) -> u64 {or(or3(a, b, c), or(d, e))}
/// An OR relation of 6 arguments.
pub fn or6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64) -> u64 {or(or3(a, b, c), or3(d, e, f))}
/// An OR relation of 7 arguments.
pub fn or7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64) -> u64 {
    or(or4(a, b, c, d), or3(e, f, g))
}
/// An OR relation of 8 arguments.
pub fn or8(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64) -> u64 {
    or(or4(a, b, c, d), or4(e, f, g, h))
}
/// An OR relation of 9 arguments.
pub fn or9(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, i: u64) -> u64 {
    or(or5(a, b, c, d, e), or4(f, g, h, i))
}
/// An OR relation of 10 arguments.
pub fn or10(
    a: u64, b: u64, c: u64, d: u64, e: u64,
    f: u64, g: u64, h: u64, i: u64, j: u64
) -> u64 {
    or(or5(a, b, c, d, e), or5(f, g, h, i, j))
}
/// An OR relation of variable number of arguments.
pub fn orn(vs: &[u64]) -> u64 {
    match vs.len() {
        0 => F,
        1 => vs[0],
        2 => or(vs[0], vs[1]),
        3 => or3(vs[0], vs[1], vs[2]),
        4 => or4(vs[0], vs[1], vs[2], vs[3]),
        5 => or5(vs[0], vs[1], vs[2], vs[3], vs[4]),
        6 => or6(vs[0], vs[1], vs[2], vs[3], vs[4], vs[5]),
        7 => or7(vs[0], vs[1], vs[2], vs[3], vs[4], vs[5], vs[6]),
        8 => or8(vs[0], vs[1], vs[2], vs[3], vs[4], vs[5], vs[6], vs[7]),
        9 => or9(vs[0], vs[1], vs[2], vs[3], vs[4], vs[5], vs[6], vs[7], vs[8]),
        10 => or10(vs[0], vs[1], vs[2], vs[3], vs[4], vs[5], vs[6], vs[7], vs[8], vs[9]),
        _ => or(orn(&vs[..10]), orn(&vs[10..]))
    }
}

/// An XOR relation of 3 arguments.
pub fn xor3(a: u64, b: u64, c: u64) -> u64 {
    or(
        and(xor(a, b), not(c)),
        not(or3(a, b, not(c)))
    )
}
/// An XOR relation of 4 arguments.
pub fn xor4(a: u64, b: u64, c: u64, d: u64) -> u64 {
    or(
        and(xor3(a, b, c), not(d)),
        not(or4(a, b, c, not(d)))
    )
}
/// An XOR relation of 5 arguments.
pub fn xor5(a: u64, b: u64, c: u64, d: u64, e: u64) -> u64 {
    or(
        and(xor4(a, b, c, d), not(e)),
        not(or5(a, b, c, d, not(e)))
    )
}
/// An XOR relation of 6 arguments.
pub fn xor6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64) -> u64 {
    or(
        and(xor5(a, b, c, d, e), not(f)),
        not(or6(a, b, c, d, e, not(f)))
    )
}
/// An XOR relation of 7 arguments.
pub fn xor7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64) -> u64 {
    or(
        and(xor6(a, b, c, d, e, f), not(g)),
        not(or7(a, b, c, d, e, f, not(g)))
    )
}
/// An XOR relation of 8 arguments.
pub fn xor8(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64) -> u64 {
    or(
        and(xor7(a, b, c, d, e, f, g), not(h)),
        not(or8(a, b, c, d, e, f, g, not(h)))
    )
}
/// An XOR relation of 9 arguments.
pub fn xor9(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, i: u64) -> u64 {
    or(
        and(xor8(a, b, c, d, e, f, g, h), not(i)),
        not(or9(a, b, c, d, e, f, g, h, not(i)))
    )
}
/// An XOR relation of 10 arguments.
pub fn xor10(
    a: u64, b: u64, c: u64, d: u64, e: u64,
    f: u64, g: u64, h: u64, i: u64, j: u64
) -> u64 {
    or(
        and(xor9(a, b, c, d, e, f, g, h, i), not(j)),
        not(or10(a, b, c, d, e, f, g, h, i, not(j)))
    )
}
/// An XOR relation of variable number of arguments.
pub fn xorn(vs: &[u64]) -> u64 {
    match vs.len() {
        0 => F,
        1 => vs[0],
        2 => xor(vs[0], vs[1]),
        3 => xor3(vs[0], vs[1], vs[2]),
        4 => xor4(vs[0], vs[1], vs[2], vs[3]),
        5 => xor5(vs[0], vs[1], vs[2], vs[3], vs[4]),
        6 => xor6(vs[0], vs[1], vs[2], vs[3], vs[4], vs[5]),
        7 => xor7(vs[0], vs[1], vs[2], vs[3], vs[4], vs[5], vs[6]),
        8 => xor8(vs[0], vs[1], vs[2], vs[3], vs[4], vs[5], vs[6], vs[7]),
        9 => xor9(vs[0], vs[1], vs[2], vs[3], vs[4], vs[5], vs[6], vs[7], vs[8]),
        10 => xor10(vs[0], vs[1], vs[2], vs[3], vs[4], vs[5], vs[6], vs[7], vs[8], vs[9]),
        x => {
            or(
                and(xorn(&vs[..x-1]), not(vs[x-1])),
                not(or(orn(&vs[..x-1]), not(vs[x-1])))
            )
        }
    }
}

/// An IMPLY chain of 3 arguments.
pub fn imply3(a: u64, b: u64, c: u64) -> u64 {and(imply(a, b), imply(b, c))}
/// An IMPLY chain of 4 arguments.
pub fn imply4(a: u64, b: u64, c: u64, d: u64) -> u64 {
    and3(imply(a, b), imply(b, c), imply(c, d))
}
/// An IMPLY chain of 5 arguments.
pub fn imply5(a: u64, b: u64, c: u64, d: u64, e: u64) -> u64 {
    and4(imply(a, b), imply(b, c), imply(c, d), imply(d, e))
}
/// An IMPLY chain of 6 arguments.
pub fn imply6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64) -> u64 {
    and5(imply(a, b), imply(b, c), imply(c, d), imply(d, e), imply(e, f))
}
/// An IMPLY chain of 7 arguments.
pub fn imply7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64) -> u64 {
    and6(imply(a, b), imply(b, c), imply(c, d), imply(d, e), imply(e, f), imply(f, g))
}
/// An IMPLY chain of 8 arguments.
pub fn imply8(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64) -> u64 {
    and7(imply(a, b), imply(b, c), imply(c, d), imply(d, e), imply(e, f), imply(f, g), imply(g, h))
}
/// An IMPLY chain of 9 arguments.
pub fn imply9(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, i: u64) -> u64 {
    and8(imply(a, b), imply(b, c), imply(c, d), imply(d, e),
         imply(e, f), imply(f, g), imply(g, h), imply(h, i))
}
/// An IMPLY chain of 10 arguments.
pub fn imply10(
    a: u64, b: u64, c: u64, d: u64, e: u64,
    f: u64, g: u64, h: u64, i: u64, j: u64,
) -> u64 {
    and9(imply(a, b), imply(b, c), imply(c, d), imply(d, e),
         imply(e, f), imply(f, g), imply(g, h), imply(h, i), imply(i, j))
}
/// An IMPLY chain of variable number of arguments.
pub fn implyn(vs: &[u64]) -> u64 {
    match vs.len() {
        0 => T,
        1 => vs[0],
        2 => imply(vs[0], vs[1]),
        3 => imply3(vs[0], vs[1], vs[2]),
        4 => imply4(vs[0], vs[1], vs[2], vs[3]),
        5 => imply5(vs[0], vs[1], vs[2], vs[3], vs[4]),
        6 => imply6(vs[0], vs[1], vs[2], vs[3], vs[4], vs[5]),
        7 => imply7(vs[0], vs[1], vs[2], vs[3], vs[4], vs[5], vs[6]),
        8 => imply8(vs[0], vs[1], vs[2], vs[3], vs[4], vs[5], vs[6], vs[7]),
        9 => imply9(vs[0], vs[1], vs[2], vs[3], vs[4], vs[5], vs[6], vs[7], vs[8]),
        10 => imply10(vs[0], vs[1], vs[2], vs[3], vs[4], vs[5], vs[6], vs[7], vs[8], vs[9]),
        x => {
            and(implyn(&vs[..x-1]), imply(vs[x-2], vs[x-1]))
        }
    }
}

/// A boolean function of one argument.
pub type Pred1 = fn(u64) -> u64;
/// A boolean function (transformed) of two arguments.
pub type Pred2 = fn(u64, u64) -> u64;

/// Implemented by types to use with `all` and `any`.
pub trait Enumerable: Sized {
    /// Returns start value.
    fn start() -> Self;
    /// Increases value.
    fn inc(&self) -> Option<Self>;
}

impl Enumerable for Pred1 {
    fn start() -> Self {false_1}
    fn inc(&self) -> Option<Self> {
        match *self {
            x if x == false_1 => Some(not),
            x if x == not => Some(id),
            x if x == id => Some(true_1),
            x if x == true_1 => None,
            _ => panic!("Unknown function"),
        }
    }
}

impl Enumerable for u8 {
    fn start() -> u8 {0}
    fn inc(&self) -> Option<Self> {self.checked_add(1)}
}

/// Enumerates the type, checking that at least one output is true.
pub fn any<E: Enumerable + Copy, F: Fn(E) -> u64>(f: &F) -> u64 {
    let mut val = E::start();
    while let Some(new_val) = E::inc(&val) {
        if f(new_val) != F {return T};
        val = new_val;
    }
    F
}

/// Enumerates the type, checking that all outputs are true.
pub fn all<E: Enumerable + Copy, F: Fn(E) -> u64>(f: &F) -> u64 {
    let mut val = E::start();
    while let Some(new_val) = E::inc(&val) {
        if f(new_val) != T {return F};
        val = new_val;
    }
    T
}

/// Implemented by provable systems of logic.
///
/// This trait is used by other crates in the PocketProver ecosystem named `pocket_prover-<name>`.
///
/// A common pattern is create logical systems that can be combined into new systems.
/// For example, a base system `Foo` is extended by `Bar<Foo>`.
/// However, `Bar<()>` might be used independently reasoning only about its own rules.
///
/// ```ignore
/// pub struct Foo<T = ()> {
///     pub bar: T,
///     pub a: u64,
///     pub b: u64,
///     pub c: u64,
/// }
///
/// impl ::std::ops::Deref for Foo<Bar> {
///     type Target = Bar;
///     fn deref(&self) -> &Bar {&self.bar}
/// }
///
/// impl Prove for Foo { ... }
/// impl Prove for Foo<Bar> { ... }
/// ```
///
/// Pro tip: Use the `Construct` and `ExtendRules` trait to auto impl this trait.
/// For base logical systems, implement the `BaseSystem` trait to auto impl this trait.
pub trait Prove: Sized + Copy {
    /// A method to count true statements.
    ///
    /// Counts `imply(<system>, f)` since this permits deriving all other methods automatically.
    fn count<F: Fn(Self) -> u64>(f: F) -> u64;

    /// A method to prove a statement according to the rules.
    ///
    /// The default method counts true cases and might be overridden for better performance.
    /// One can compute the number of true cases faster by using `1 << bits`.
    fn prove<F: Fn(Self) -> u64>(f: F) -> bool {
        Self::count(f) == Self::count(|_| T)
    }

    /// According to the rules, the assumption does not lead to the conclusion,
    /// but neither does it lead to the opposite conclusion.
    fn does_not_mean<F: Fn(Self) -> u64, G: Fn(Self) -> u64>(
        assumption: F, conclusion: G
    ) -> bool {
        !Self::prove(|x| imply(assumption(x), conclusion(x))) &&
        !Self::prove(|x| imply(assumption(x), not(conclusion(x))))
    }

    /// According to the rules, the conclusion follows from the assumptions,
    /// but the assumptions can not be used to get the opposite conclusion.
    fn means<F: Fn(Self) -> u64, G: Fn(Self) -> u64>(assumption: F, conclusion: G) -> bool {
        Self::prove(|x| imply(assumption(x), conclusion(x))) &&
        !Self::prove(|x| imply(assumption(x), not(conclusion(x))))
    }

    /// Proves that according to the rules, two statements are equivalent.
    fn eq<F: Fn(Self) -> u64, G: Fn(Self) -> u64>(a: F, b: G) -> bool {
        Self::prove(|x| eq(a(x), b(x)))
    }

    /// Proves that according to the rules, two statements are exclusive.
    fn exc<F: Fn(Self) -> u64, G: Fn(Self) -> u64>(a: F, b: G) -> bool {
        Self::prove(|x| and(
            imply(a(x), not(b(x))),
            imply(b(x), not(a(x)))
        ))
    }

    /// Proves that according to the rules, the first statement implies the other.
    fn imply<F: Fn(Self) -> u64, G: Fn(Self) -> u64>(a: F, b: G) -> bool {
        Self::prove(|x| imply(a(x), b(x)))
    }

    /// Computes the logical probability `P(f | rules)`.
    fn prob<F: Fn(Self) -> u64>(f: F) -> Option<f64> {
        // Get the number of cases when the system implies falsehood.
        // This is an indirect way of counting cases when the rules are true.
        let fa = Self::count(|_| F);
        let tr = Self::count(|_| T);
        let full_rules = tr - fa;
        if full_rules == 0 {return None}
        else {
            Some((Self::count(f) - fa) as f64 / full_rules as f64)
        }
    }

    /// Computes the logical probability `P(b | a ∧ rules)`.
    fn prob_imply<A: Fn(Self) -> u64 + Copy, B: Fn(Self) -> u64>(a: A, b: B) -> Option<f64> {
        let fa = Self::count(|_| F);
        let count_a = Self::count(a) - fa;
        if count_a == 0 {return None}
        else {
            Some((Self::count(|x| and(a(x), b(x))) - fa) as f64 / count_a as f64)
        }
    }
}

impl<T> Prove for T where T: Copy + Construct + ExtendRules {
    fn count<F: Fn(Self) -> u64>(f: F) -> u64 {
        countn(<Self as Construct>::n(), &mut |vs| {
            let v: Self = Construct::construct(vs);
            imply(v.full_rules(), f(v))
        })
    }

    fn prove<F: Fn(Self) -> u64>(f: F) -> bool {
        Self::count(f) == 1 << <Self as Construct>::n()
    }
}

/// Implemented by logical systems to define core rules.
pub trait CoreRules {
    /// The core rules of the logical system.
    fn core_rules(&self) -> u64;
}

/// Implemented by logical systems to extend existing ones.
pub trait ExtendRules: CoreRules {
    /// The inner logical system.
    type Inner: ExtendRules;
    /// Gets the inner logical system.
    fn inner(&self) -> &Self::Inner;
    /// Rules used to integrate with inner logical system.
    fn extend_rules(&self, inner: &Self::Inner) -> u64;

    /// The full rules of the entire logical system.
    fn full_rules(&self) -> u64 {
        and3(self.core_rules(), self.extend_rules(self.inner()), self.inner().full_rules())
    }
}

/// Implemented by base logical systems.
///
/// Auto impls the `ExtendRules` trait and therefore also the `Prove` trait.
pub trait BaseSystem: Construct + CoreRules {}

impl<T> ExtendRules for T where T: BaseSystem {
    type Inner = ();
    fn inner(&self) -> &() {&()}
    fn extend_rules(&self, _: &Self::Inner) -> u64 {T}
}

impl CoreRules for () {
    fn core_rules(&self) -> u64 {T}
}

impl<T0: CoreRules, T1: CoreRules> CoreRules for (T0, T1) {
    fn core_rules(&self) -> u64 {
        and(self.0.core_rules(), self.1.core_rules())
    }
}

impl<T0, T1, T2> CoreRules for (T0, T1, T2)
    where T0: CoreRules, T1: CoreRules, T2: CoreRules
{
    fn core_rules(&self) -> u64 {
        and3(
            self.0.core_rules(),
            self.1.core_rules(),
            self.2.core_rules(),
        )
    }
}

impl<T0, T1, T2, T3> CoreRules for (T0, T1, T2, T3)
    where T0: CoreRules, T1: CoreRules,
          T2: CoreRules, T3: CoreRules,
{
    fn core_rules(&self) -> u64 {
        and4(
            self.0.core_rules(),
            self.1.core_rules(),
            self.2.core_rules(),
            self.3.core_rules(),
        )
    }
}

impl<T0, T1, T2, T3, T4> CoreRules for (T0, T1, T2, T3, T4)
    where T0: CoreRules, T1: CoreRules,
          T2: CoreRules, T3: CoreRules,
          T4: CoreRules,
{
    fn core_rules(&self) -> u64 {
        and5(
            self.0.core_rules(),
            self.1.core_rules(),
            self.2.core_rules(),
            self.3.core_rules(),
            self.4.core_rules(),
        )
    }
}

impl<T0, T1, T2, T3, T4, T5> CoreRules for (T0, T1, T2, T3, T4, T5)
    where T0: CoreRules, T1: CoreRules,
          T2: CoreRules, T3: CoreRules,
          T4: CoreRules, T5: CoreRules,
{
    fn core_rules(&self) -> u64 {
        and6(
            self.0.core_rules(),
            self.1.core_rules(),
            self.2.core_rules(),
            self.3.core_rules(),
            self.4.core_rules(),
            self.5.core_rules(),
        )
    }
}

impl<T0, T1, T2, T3, T4, T5, T6> CoreRules for (T0, T1, T2, T3, T4, T5, T6)
    where T0: CoreRules, T1: CoreRules,
          T2: CoreRules, T3: CoreRules,
          T4: CoreRules, T5: CoreRules,
          T6: CoreRules,
{
    fn core_rules(&self) -> u64 {
        and7(
            self.0.core_rules(),
            self.1.core_rules(),
            self.2.core_rules(),
            self.3.core_rules(),
            self.4.core_rules(),
            self.5.core_rules(),
            self.6.core_rules(),
        )
    }
}

impl<T0, T1, T2, T3, T4, T5, T6, T7> CoreRules for (T0, T1, T2, T3, T4, T5, T6, T7)
    where T0: CoreRules, T1: CoreRules,
          T2: CoreRules, T3: CoreRules,
          T4: CoreRules, T5: CoreRules,
          T6: CoreRules, T7: CoreRules,
{
    fn core_rules(&self) -> u64 {
        and8(
            self.0.core_rules(),
            self.1.core_rules(),
            self.2.core_rules(),
            self.3.core_rules(),
            self.4.core_rules(),
            self.5.core_rules(),
            self.6.core_rules(),
            self.7.core_rules(),
        )
    }
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8> CoreRules for (T0, T1, T2, T3, T4, T5, T6, T7, T8)
    where T0: CoreRules, T1: CoreRules,
          T2: CoreRules, T3: CoreRules,
          T4: CoreRules, T5: CoreRules,
          T6: CoreRules, T7: CoreRules,
          T8: CoreRules,
{
    fn core_rules(&self) -> u64 {
        and9(
            self.0.core_rules(),
            self.1.core_rules(),
            self.2.core_rules(),
            self.3.core_rules(),
            self.4.core_rules(),
            self.5.core_rules(),
            self.6.core_rules(),
            self.7.core_rules(),
            self.8.core_rules(),
        )
    }
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> CoreRules for (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9)
    where T0: CoreRules, T1: CoreRules,
          T2: CoreRules, T3: CoreRules,
          T4: CoreRules, T5: CoreRules,
          T6: CoreRules, T7: CoreRules,
          T8: CoreRules, T9: CoreRules,
{
    fn core_rules(&self) -> u64 {
        and10(
            self.0.core_rules(),
            self.1.core_rules(),
            self.2.core_rules(),
            self.3.core_rules(),
            self.4.core_rules(),
            self.5.core_rules(),
            self.6.core_rules(),
            self.7.core_rules(),
            self.8.core_rules(),
            self.9.core_rules(),
        )
    }
}

impl ExtendRules for () {
    type Inner = ();
    fn inner(&self) -> &() {&()}
    fn extend_rules(&self, _: &()) -> u64 {T}
    fn full_rules(&self) -> u64 {T}
}

impl<T0: ExtendRules, T1: ExtendRules> ExtendRules for (T0, T1) {
    type Inner = ();
    fn inner(&self) -> &() {&()}
    fn extend_rules(&self, _: &()) -> u64 {T}
}

impl<T0, T1, T2> ExtendRules for (T0, T1, T2)
    where T0: ExtendRules, T1: ExtendRules, T2: ExtendRules
{
    type Inner = ();
    fn inner(&self) -> &() {&()}
    fn extend_rules(&self, _: &()) -> u64 {T}
}

impl<T0, T1, T2, T3> ExtendRules for (T0, T1, T2, T3)
    where T0: ExtendRules, T1: ExtendRules,
          T2: ExtendRules, T3: ExtendRules
{
    type Inner = ();
    fn inner(&self) -> &() {&()}
    fn extend_rules(&self, _: &()) -> u64 {T}
}

impl<T0, T1, T2, T3, T4> ExtendRules for (T0, T1, T2, T3, T4)
    where T0: ExtendRules, T1: ExtendRules,
          T2: ExtendRules, T3: ExtendRules,
          T4: ExtendRules,
{
    type Inner = ();
    fn inner(&self) -> &() {&()}
    fn extend_rules(&self, _: &()) -> u64 {T}
}

impl<T0, T1, T2, T3, T4, T5> ExtendRules for (T0, T1, T2, T3, T4, T5)
    where T0: ExtendRules, T1: ExtendRules,
          T2: ExtendRules, T3: ExtendRules,
          T4: ExtendRules, T5: ExtendRules,
{
    type Inner = ();
    fn inner(&self) -> &() {&()}
    fn extend_rules(&self, _: &()) -> u64 {T}
}

impl<T0, T1, T2, T3, T4, T5, T6> ExtendRules for (T0, T1, T2, T3, T4, T5, T6)
    where T0: ExtendRules, T1: ExtendRules,
          T2: ExtendRules, T3: ExtendRules,
          T4: ExtendRules, T5: ExtendRules,
          T6: ExtendRules,
{
    type Inner = ();
    fn inner(&self) -> &() {&()}
    fn extend_rules(&self, _: &()) -> u64 {T}
}

impl<T0, T1, T2, T3, T4, T5, T6, T7> ExtendRules for (T0, T1, T2, T3, T4, T5, T6, T7)
    where T0: ExtendRules, T1: ExtendRules,
          T2: ExtendRules, T3: ExtendRules,
          T4: ExtendRules, T5: ExtendRules,
          T6: ExtendRules, T7: ExtendRules,
{
    type Inner = ();
    fn inner(&self) -> &() {&()}
    fn extend_rules(&self, _: &()) -> u64 {T}
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8> ExtendRules for (T0, T1, T2, T3, T4, T5, T6, T7, T8)
    where T0: ExtendRules, T1: ExtendRules,
          T2: ExtendRules, T3: ExtendRules,
          T4: ExtendRules, T5: ExtendRules,
          T6: ExtendRules, T7: ExtendRules,
          T8: ExtendRules,
{
    type Inner = ();
    fn inner(&self) -> &() {&()}
    fn extend_rules(&self, _: &()) -> u64 {T}
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> ExtendRules
for (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9)
    where T0: ExtendRules, T1: ExtendRules,
          T2: ExtendRules, T3: ExtendRules,
          T4: ExtendRules, T5: ExtendRules,
          T6: ExtendRules, T7: ExtendRules,
          T8: ExtendRules, T9: ExtendRules,
{
    type Inner = ();
    fn inner(&self) -> &() {&()}
    fn extend_rules(&self, _: &()) -> u64 {T}
}


/// Used to construct logical systems.
pub trait Construct: Sized {
    /// Creates a logical system out of proof arguments.
    fn construct(vs: &[u64]) -> Self;

    /// Gets the number of bits in logical system.
    fn n() -> usize {
        use std::mem::size_of;
        size_of::<Self>() / size_of::<u64>()
    }
}

impl Construct for () {
    fn construct(_vs: &[u64]) -> Self {()}
}

impl<T0: Construct, T1: Construct> Construct for (T0, T1) {
    fn construct(vs: &[u64]) -> Self {
        let n = <T0 as Construct>::n();
        (Construct::construct(vs), Construct::construct(&vs[n..]))
    }
}

impl<T0, T1, T2> Construct for (T0, T1, T2)
    where T0: Construct, T1: Construct, T2: Construct
{
    fn construct(vs: &[u64]) -> Self {
        let n0 = <T0 as Construct>::n();
        let n1 = <T1 as Construct>::n() + n0;
        (
            Construct::construct(vs),
            Construct::construct(&vs[n0..]),
            Construct::construct(&vs[n1..])
        )
    }
}

impl<T0, T1, T2, T3> Construct for (T0, T1, T2, T3)
    where T0: Construct, T1: Construct, T2: Construct, T3: Construct
{
    fn construct(vs: &[u64]) -> Self {
        let n0 = <T0 as Construct>::n();
        let n1 = <T1 as Construct>::n() + n0;
        let n2 = <T2 as Construct>::n() + n1;
        (
            Construct::construct(vs),
            Construct::construct(&vs[n0..]),
            Construct::construct(&vs[n1..]),
            Construct::construct(&vs[n2..])
        )
    }
}

impl<T0, T1, T2, T3, T4> Construct for (T0, T1, T2, T3, T4)
    where T0: Construct, T1: Construct,
          T2: Construct, T3: Construct,
          T4: Construct
{
    fn construct(vs: &[u64]) -> Self {
        let n0 = <T0 as Construct>::n();
        let n1 = <T1 as Construct>::n() + n0;
        let n2 = <T2 as Construct>::n() + n1;
        let n3 = <T3 as Construct>::n() + n2;
        (
            Construct::construct(vs),
            Construct::construct(&vs[n0..]),
            Construct::construct(&vs[n1..]),
            Construct::construct(&vs[n2..]),
            Construct::construct(&vs[n3..])
        )
    }
}

impl<T0, T1, T2, T3, T4, T5> Construct for (T0, T1, T2, T3, T4, T5)
    where T0: Construct, T1: Construct,
          T2: Construct, T3: Construct,
          T4: Construct, T5: Construct,
{
    fn construct(vs: &[u64]) -> Self {
        let n0 = <T0 as Construct>::n();
        let n1 = <T1 as Construct>::n() + n0;
        let n2 = <T2 as Construct>::n() + n1;
        let n3 = <T3 as Construct>::n() + n2;
        let n4 = <T4 as Construct>::n() + n3;
        (
            Construct::construct(vs),
            Construct::construct(&vs[n0..]),
            Construct::construct(&vs[n1..]),
            Construct::construct(&vs[n2..]),
            Construct::construct(&vs[n3..]),
            Construct::construct(&vs[n4..])
        )
    }
}

impl<T0, T1, T2, T3, T4, T5, T6> Construct for (T0, T1, T2, T3, T4, T5, T6)
    where T0: Construct, T1: Construct,
          T2: Construct, T3: Construct,
          T4: Construct, T5: Construct,
          T6: Construct
{
    fn construct(vs: &[u64]) -> Self {
        let n0 = <T0 as Construct>::n();
        let n1 = <T1 as Construct>::n() + n0;
        let n2 = <T2 as Construct>::n() + n1;
        let n3 = <T3 as Construct>::n() + n2;
        let n4 = <T4 as Construct>::n() + n3;
        let n5 = <T5 as Construct>::n() + n4;
        (
            Construct::construct(vs),
            Construct::construct(&vs[n0..]),
            Construct::construct(&vs[n1..]),
            Construct::construct(&vs[n2..]),
            Construct::construct(&vs[n3..]),
            Construct::construct(&vs[n4..]),
            Construct::construct(&vs[n5..])
        )
    }
}

impl<T0, T1, T2, T3, T4, T5, T6, T7> Construct for (T0, T1, T2, T3, T4, T5, T6, T7)
    where T0: Construct, T1: Construct,
          T2: Construct, T3: Construct,
          T4: Construct, T5: Construct,
          T6: Construct, T7: Construct
{
    fn construct(vs: &[u64]) -> Self {
        let n0 = <T0 as Construct>::n();
        let n1 = <T1 as Construct>::n() + n0;
        let n2 = <T2 as Construct>::n() + n1;
        let n3 = <T3 as Construct>::n() + n2;
        let n4 = <T4 as Construct>::n() + n3;
        let n5 = <T5 as Construct>::n() + n4;
        let n6 = <T6 as Construct>::n() + n5;
        (
            Construct::construct(vs),
            Construct::construct(&vs[n0..]),
            Construct::construct(&vs[n1..]),
            Construct::construct(&vs[n2..]),
            Construct::construct(&vs[n3..]),
            Construct::construct(&vs[n4..]),
            Construct::construct(&vs[n5..]),
            Construct::construct(&vs[n6..])
        )
    }
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8> Construct for (T0, T1, T2, T3, T4, T5, T6, T7, T8)
    where T0: Construct, T1: Construct,
          T2: Construct, T3: Construct,
          T4: Construct, T5: Construct,
          T6: Construct, T7: Construct,
          T8: Construct
{
    fn construct(vs: &[u64]) -> Self {
        let n0 = <T0 as Construct>::n();
        let n1 = <T1 as Construct>::n() + n0;
        let n2 = <T2 as Construct>::n() + n1;
        let n3 = <T3 as Construct>::n() + n2;
        let n4 = <T4 as Construct>::n() + n3;
        let n5 = <T5 as Construct>::n() + n4;
        let n6 = <T6 as Construct>::n() + n5;
        let n7 = <T7 as Construct>::n() + n6;
        (
            Construct::construct(vs),
            Construct::construct(&vs[n0..]),
            Construct::construct(&vs[n1..]),
            Construct::construct(&vs[n2..]),
            Construct::construct(&vs[n3..]),
            Construct::construct(&vs[n4..]),
            Construct::construct(&vs[n5..]),
            Construct::construct(&vs[n6..]),
            Construct::construct(&vs[n7..])
        )
    }
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> Construct for (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9)
    where T0: Construct, T1: Construct,
          T2: Construct, T3: Construct,
          T4: Construct, T5: Construct,
          T6: Construct, T7: Construct,
          T8: Construct, T9: Construct
{
    fn construct(vs: &[u64]) -> Self {
        let n0 = <T0 as Construct>::n();
        let n1 = <T1 as Construct>::n() + n0;
        let n2 = <T2 as Construct>::n() + n1;
        let n3 = <T3 as Construct>::n() + n2;
        let n4 = <T4 as Construct>::n() + n3;
        let n5 = <T5 as Construct>::n() + n4;
        let n6 = <T6 as Construct>::n() + n5;
        let n7 = <T7 as Construct>::n() + n6;
        let n8 = <T8 as Construct>::n() + n7;
        (
            Construct::construct(vs),
            Construct::construct(&vs[n0..]),
            Construct::construct(&vs[n1..]),
            Construct::construct(&vs[n2..]),
            Construct::construct(&vs[n3..]),
            Construct::construct(&vs[n4..]),
            Construct::construct(&vs[n5..]),
            Construct::construct(&vs[n6..]),
            Construct::construct(&vs[n7..]),
            Construct::construct(&vs[n8..])
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_2() {
        assert_eq!(count1(&mut false_1), 0);
        assert_eq!(count1(&mut not), 1);
        assert_eq!(count1(&mut id), 1);
        assert_eq!(count1(&mut true_1), 2);

        assert_eq!(count2(&mut false_2), 0);
        assert_eq!(count2(&mut and), 1);
        assert_eq!(count2(&mut xor), 2);
        assert_eq!(count2(&mut eq), 2);
        assert_eq!(count2(&mut or), 3);
        assert_eq!(count2(&mut true_2), 4);
        assert_eq!(count2(&mut imply), 3);
        assert_eq!(count2(&mut |a, b| imply(and(a, b), or(a, b))), 4);

        assert_eq!(count3(&mut |a, b, c| and(or(a, b), and(a, c))), 2);
        assert_eq!(count4(&mut |a, b, c, d| and(or(a, b), or(c, d))), 9);
        assert_eq!(count5(&mut |_, _, _, _, _| T), 32);
        assert_eq!(count6(&mut |_, _, _, _, _, _| T), 64);
        assert_eq!(count7(&mut |_, _, _, _, _, _, _| T), 128);
        assert_eq!(count8(&mut |_, _, _, _, _, _, _, _| T), 256);
        assert_eq!(count9(&mut |_, _, _, _, _, _, _, _, _| T), 512);
        assert_eq!(count10(&mut |_, _, _, _, _, _, _, _, _, _| T), 1024);
    }
}

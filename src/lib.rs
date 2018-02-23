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
//!     println!("Socrates is mortal: {}", prove3(&mut |man, mortal, socrates| {
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
/// The False proposition.
/// Used to alternate higher than 6 arguments, set to `0`.
pub const F: u64 = 0b00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000;
/// The True proposition.
/// Used to alternate higher than 6 arguments, set to `1`.
pub const T: u64 = 0b11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111;

/// Counts the number of solutions of a 1-argument boolean function.
pub fn count1<F: FnMut(u64) -> u64>(f: &mut F) -> u32 {((f)(P0) & 0x3).count_ones()}
/// Counts the number of solutions of a 2-argument boolean function.
pub fn count2<F: FnMut(u64, u64) -> u64>(f: &mut F) -> u32 {((f)(P0, P1) & 0xf).count_ones()}
/// Counts the number of solutions of a 3-argument boolean function.
pub fn count3<F: FnMut(u64, u64, u64) -> u64>(f: &mut F) -> u32 {((f)(P0, P1, P2) & 0xff).count_ones()}
/// Counts the number of solutions of a 4-argument boolean function.
pub fn count4<F: FnMut(u64, u64, u64, u64) -> u64>(f: &mut F) -> u32 {((f)(P0, P1, P2, P3) & 0xffff).count_ones()}
/// Counts the number of solutions of a 5-argument boolean function.
pub fn count5<F: FnMut(u64, u64, u64, u64, u64) -> u64>(f: &mut F) -> u32 {
    ((f)(P0, P1, P2, P3, P4) & 0xffff_ffff).count_ones()
}
/// Counts the number of solutions of a 6-argument boolean function.
pub fn count6<F: FnMut(u64, u64, u64, u64, u64, u64) -> u64>(f: &mut F) -> u32 {
    (f)(P0, P1, P2, P3, P4, P5).count_ones()
}
/// Counts the number of solutions of a 7-argument boolean function.
pub fn count7<F: FnMut(u64, u64, u64, u64, u64, u64, u64) -> u64>(f: &mut F) -> u32 {
    (f)(P0, P1, P2, P3, P4, P5, F).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, T).count_ones()
}
/// Counts the number of solutions of an 8-argument boolean function.
pub fn count8<F: FnMut(u64, u64, u64, u64, u64, u64, u64, u64) -> u64>(f: &mut F) -> u32 {
    (f)(P0, P1, P2, P3, P4, P5, F, F).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, F, T).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, T, F).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, T, T).count_ones()
}
/// Counts the number of solutions of a 9-argument boolean function.
pub fn count9<F: FnMut(u64, u64, u64, u64, u64, u64, u64, u64, u64) -> u64>(f: &mut F) -> u32 {
    (f)(P0, P1, P2, P3, P4, P5, F, F, F).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, F, F, T).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, F, T, F).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, F, T, T).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, T, F, F).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, T, F, T).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, T, T, F).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, T, T, T).count_ones()
}
/// Counts the number of solutions of a 10-argument boolean function.
pub fn count10<F: FnMut(u64, u64, u64, u64, u64, u64, u64, u64, u64, u64) -> u64>(f: &mut F) -> u32 {
    (f)(P0, P1, P2, P3, P4, P5, F, F, F, F).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, F, F, F, T).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, F, F, T, F).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, F, F, T, T).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, F, T, F, F).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, F, T, F, T).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, F, T, T, F).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, F, T, T, T).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, T, F, F, F).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, T, F, F, T).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, T, F, T, F).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, T, F, T, T).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, T, T, F, F).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, T, T, F, T).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, T, T, T, F).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, T, T, T, T).count_ones()
}
/// Counts the number of solutions of an n-argument boolean function.
pub fn countn(n: usize, fun: &mut FnMut(&[u64]) -> u64) -> u64 {
    match n {
        0 => fun(&[]).count_ones() as u64,
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
                        fun(&args)
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
                        fun(&args)
                    });
                }
                sum
            }
        }
    }
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

/// And and relation of 3 argument.
pub fn and3(a: u64, b: u64, c: u64) -> u64 {and(and(a, b), c)}
/// An and relation of 4 arguments.
pub fn and4(a: u64, b: u64, c: u64, d: u64) -> u64 {and(and(a, b), and(c, d))}
/// An and relation of 5 arguments.
pub fn and5(a: u64, b: u64, c: u64, d: u64, e: u64) -> u64 {and(and(a, b), and3(c, d, e))}
/// An and relation of 6 arguments.
pub fn and6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64) -> u64 {
    and(and3(a, b, c), and3(d, e, f))
}
/// An and relation of 7 arguments.
pub fn and7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64) -> u64 {
    and(and4(a, b, c, d), and3(e, f, g))
}
/// An and relation of 8 arguments.
pub fn and8(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64) -> u64 {
    and(and4(a, b, c, d), and4(e, f, g, h))
}
/// An and relation of 9 arguments.
pub fn and9(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, i: u64) -> u64 {
    and(and5(a, b, c, d, e), and4(f, g, h, i))
}
/// An and relation of 10 arguments.
pub fn and10(
    a: u64, b: u64, c: u64, d: u64, e: u64,
    f: u64, g: u64, h: u64, i: u64, j: u64
) -> u64 {
    and(and5(a, b, c, d, e), and5(f, g, h, i, j))
}
/// An and relation of variable number of arguments.
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
        x => and(andn(&vs[..x]), andn(&vs[x..]))
    }
}

/// An or relation of 3 arguments.
pub fn or3(a: u64, b: u64, c: u64) -> u64 {or(or(a, b), c)}
/// An or relation of 4 arguments.
pub fn or4(a: u64, b: u64, c: u64, d: u64) -> u64 {or(or(a, b), or(c, d))}
/// An or relation of 5 arguments.
pub fn or5(a: u64, b: u64, c: u64, d: u64, e: u64) -> u64 {or(or3(a, b, c), or(d, e))}
/// An or relation of 6 arguments.
pub fn or6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64) -> u64 {or(or3(a, b, c), or3(d, e, f))}
/// An or relation of 7 arguments.
pub fn or7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64) -> u64 {
    or(or4(a, b, c, d), or3(e, f, g))
}
/// An or relation of 8 arguments.
pub fn or8(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64) -> u64 {
    or(or4(a, b, c, d), or4(e, f, g, h))
}
/// An or relation of 9 arguments.
pub fn or9(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, i: u64) -> u64 {
    or(or5(a, b, c, d, e), or4(f, g, h, i))
}
/// An or relation of 10 arguments.
pub fn or10(
    a: u64, b: u64, c: u64, d: u64, e: u64,
    f: u64, g: u64, h: u64, i: u64, j: u64
) -> u64 {
    or(or5(a, b, c, d, e), or5(f, g, h, i, j))
}
/// An or relation of variable number of arguments.
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
        x => or(orn(&vs[..x]), orn(&vs[x..]))
    }
}

/// An xor relation of 3 arguments.
pub fn xor3(a: u64, b: u64, c: u64) -> u64 {
    or(
        and(xor(a, b), not(c)),
        not(or3(a, b, not(c)))
    )
}
/// An xor relation of 4 arguments.
pub fn xor4(a: u64, b: u64, c: u64, d: u64) -> u64 {
    or(
        and(xor3(a, b, c), not(d)),
        not(or4(a, b, c, not(d)))
    )
}
/// An xor relation of 5 arguments.
pub fn xor5(a: u64, b: u64, c: u64, d: u64, e: u64) -> u64 {
    or(
        and(xor4(a, b, c, d), not(e)),
        not(or5(a, b, c, d, not(e)))
    )
}
/// An xor relation of 6 arguments.
pub fn xor6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64) -> u64 {
    or(
        and(xor5(a, b, c, d, e), not(f)),
        not(or6(a, b, c, d, e, not(f)))
    )
}
/// An xor relation of 7 arguments.
pub fn xor7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64) -> u64 {
    or(
        and(xor6(a, b, c, d, e, f), not(g)),
        not(or7(a, b, c, d, e, f, not(g)))
    )
}
/// An xor relation of 8 arguments.
pub fn xor8(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64) -> u64 {
    or(
        and(xor7(a, b, c, d, e, f, g), not(h)),
        not(or8(a, b, c, d, e, f, g, not(h)))
    )
}
/// An xor relation of 9 arguments.
pub fn xor9(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, i: u64) -> u64 {
    or(
        and(xor8(a, b, c, d, e, f, g, h), not(i)),
        not(or9(a, b, c, d, e, f, g, h, not(i)))
    )
}
/// An xor relation of 10 arguments.
pub fn xor10(
    a: u64, b: u64, c: u64, d: u64, e: u64,
    f: u64, g: u64, h: u64, i: u64, j: u64
) -> u64 {
    or(
        and(xor9(a, b, c, d, e, f, g, h, i), not(j)),
        not(or10(a, b, c, d, e, f, g, h, i, not(j)))
    )
}
/// An xor relation of variable number of arguments.
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
                and(xorn(&vs[..x]), not(vs[x-1])),
                not(or(orn(&vs[..x]), not(vs[x-1])))
            )
        }
    }
}

/// An imply chain of 3 arguments.
pub fn imply3(a: u64, b: u64, c: u64) -> u64 {and(imply(a, b), imply(b, c))}
/// An imply chain of 4 arguments.
pub fn imply4(a: u64, b: u64, c: u64, d: u64) -> u64 {
    and3(imply(a, b), imply(b, c), imply(c, d))
}
/// An imply chain of 5 arguments.
pub fn imply5(a: u64, b: u64, c: u64, d: u64, e: u64) -> u64 {
    and4(imply(a, b), imply(b, c), imply(c, d), imply(d, e))
}
/// An imply chain of 6 arguments.
pub fn imply6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64) -> u64 {
    and5(imply(a, b), imply(b, c), imply(c, d), imply(d, e), imply(e, f))
}
/// An imply chain of 7 arguments.
pub fn imply7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64) -> u64 {
    and6(imply(a, b), imply(b, c), imply(c, d), imply(d, e), imply(e, f), imply(f, g))
}
/// An imply chain of 8 arguments.
pub fn imply8(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64) -> u64 {
    and7(imply(a, b), imply(b, c), imply(c, d), imply(d, e), imply(e, f), imply(f, g), imply(g, h))
}
/// An imply chain of 9 arguments.
pub fn imply9(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, i: u64) -> u64 {
    and8(imply(a, b), imply(b, c), imply(c, d), imply(d, e),
         imply(e, f), imply(f, g), imply(g, h), imply(h, i))
}
/// An imply chain of 10 arguments.
pub fn imply10(
    a: u64, b: u64, c: u64, d: u64, e: u64,
    f: u64, g: u64, h: u64, i: u64, j: u64,
) -> u64 {
    and9(imply(a, b), imply(b, c), imply(c, d), imply(d, e),
         imply(e, f), imply(f, g), imply(g, h), imply(h, i), imply(i, j))
}
/// An imply chain of variable number of arguments.
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
            and(implyn(&vs[..x]), imply(vs[x-2], vs[x-1]))
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

//! Helper utilities for extracting data from proofs.
//!
//! ```rust
//! use pocket_prover::*;
//!
//! fn main() {
//!     println!("(a ∧ c) (b ∧ c) (∃)");
//!     println_extract!(
//!         &mut |a, b, c| and(eq(a, b), c);
//!         x0 => and(a, c),
//!         x1 => and(b, c)
//!     );
//!
//!     println!("");
//!     println!("By looking at the table above one can see that `a ∧ c` and `b ∧ c` are equal.");
//!     println!("Therefore, one can prove:");
//!     println!("");
//!     println!("   (a = b) ∧ c");
//!     println!("-----------------");
//!     println!("(a ∧ c) = (b ∧ c)");
//!     println!("");
//!     println!("Result: {}", prove!(&mut |a, b, c| {
//!         imply(
//!             and(eq(a, b), c),
//!             eq(and(a, c), and(b, c))
//!         )
//!     }))
//! }
//! ```

use crate::{id, not};

/// Converts a boolean to a bit.
pub fn bit(b: bool) -> u64 {if b {1} else {0}}

/// Converts a bit to a boolean.
pub fn bitv(b: u64) -> bool {b != 0}

/// If the bit argument is `0`, returns `not`, else `id`.
pub fn bitf(b: u64) -> fn(u64) -> u64 {if b == 0 {not} else {id}}

/// Generates a "{}{}{}..." format for bits.
#[macro_export]
macro_rules! bits_format(
    ($x:ident) => {"{}"};
    ($x:ident , $($y:ident),*) => {concat!("{}", bits_format!($($y),*))};
);

/// Evaluates an expression for all bit configurations.
#[macro_export]
macro_rules! bits(
    (|$($x:ident),* $(,)?| $e:expr) => {
        let _n = tup_count!($($x),*);
        for _x in 0_u64..(1 << _n) {
            let mut _i = 0;
            $(let $x = (_x >> (_n - _i - 1)) & 1; _i += 1;)*
            $e
        }
    }
);

/// Prints a truth table with result of a boolean expression.
#[macro_export]
macro_rules! println_bits(
    (|$($x:ident),* $(,)?| $e:expr) => {
        bits!(|$($x),*| {
            println!(concat!(bits_format!($($x),*), " {}"), $($x),*, $crate::extract::bit($e));
        });
    }
);

/// Prints a truth table extracted from a theory,
/// assigning each case a bit and automatically flip expression properly.
#[macro_export]
macro_rules! println_extract(
    (&mut |$($t:ident),* $(,)?| $th:expr ; $($x:ident => $ch:expr),* $(,)?) => {
        println_bits!(|$($x),*| {
            !prove!(&mut |$($t),*| {
                imply(
                    $th,
                    not(and!($($crate::extract::bitf($x)($ch)),*))
                )
            })
        });
    };
    (&mut |($($t1:ident),+ $(,)?), ($($t0:ident),+ $(,)?)| $th:expr ; $($x:ident => $ch:expr),* $(,)?) => {
        println_bits!(|$($x),*| {
            !prove!(&mut |($($t1),+), ($($t0),+)| {
                imply(
                    $th,
                    not(and!($($crate::extract::bitf($x)($ch)),*))
                )
            })
        });
    };
);

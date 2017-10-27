
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
pub fn count1<F: Fn(u64) -> u64>(f: F) -> u32 {((f)(P0) & 0x3).count_ones()}
/// Counts the number of solutions of a 2-argument boolean function.
pub fn count2<F: Fn(u64, u64) -> u64>(f: F) -> u32 {((f)(P0, P1) & 0xf).count_ones()}
/// Counts the number of solutions of a 3-argument boolean function.
pub fn count3<F: Fn(u64, u64, u64) -> u64>(f: F) -> u32 {((f)(P0, P1, P2) & 0xff).count_ones()}
/// Counts the number of solutions of a 4-argument boolean function.
pub fn count4<F: Fn(u64, u64, u64, u64) -> u64>(f: F) -> u32 {((f)(P0, P1, P2, P3) & 0xffff).count_ones()}
/// Counts the number of solutions of a 5-argument boolean function.
pub fn count5<F: Fn(u64, u64, u64, u64, u64) -> u64>(f: F) -> u32 {
    ((f)(P0, P1, P2, P3, P4) & 0xffff_ffff).count_ones()
}
/// Counts the number of solutions of a 6-argument boolean function.
pub fn count6<F: Fn(u64, u64, u64, u64, u64, u64) -> u64>(f: F) -> u32 {
    (f)(P0, P1, P2, P3, P4, P5).count_ones()
}
/// Counts the number of solutions of a 7-argument boolean function.
pub fn count7<F: Fn(u64, u64, u64, u64, u64, u64, u64) -> u64>(f: F) -> u32 {
    (f)(P0, P1, P2, P3, P4, P5, F).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, T).count_ones()
}
/// Counts the number of solutions of an 8-argument boolean function.
pub fn count8<F: Fn(u64, u64, u64, u64, u64, u64, u64, u64) -> u64>(f: F) -> u32 {
    (f)(P0, P1, P2, P3, P4, P5, F, F).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, F, T).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, T, F).count_ones() +
    (f)(P0, P1, P2, P3, P4, P5, T, T).count_ones()
}
/// Counts the number of solutions of a 9-argument boolean function.
pub fn count9<F: Fn(u64, u64, u64, u64, u64, u64, u64, u64, u64) -> u64>(f: F) -> u32 {
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
pub fn count10<F: Fn(u64, u64, u64, u64, u64, u64, u64, u64, u64, u64) -> u64>(f: F) -> u32 {
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

/// Returns `true` if proposition is correct, `false` otherwise.
pub fn prove1<F: Fn(u64) -> u64>(f: F) -> bool {count1(f) == 2}
/// Returns `true` if proposition is correct, `false` otherwise.
pub fn prove2<F: Fn(u64, u64) -> u64>(f: F) -> bool {count2(f) == 4}
/// Returns `true` if proposition is correct, `false` otherwise.
pub fn prove3<F: Fn(u64, u64, u64) -> u64>(f: F) -> bool {count3(f) == 8}
/// Returns `true` if proposition is correct, `false` otherwise.
pub fn prove4<F: Fn(u64, u64, u64, u64) -> u64>(f: F) -> bool {count4(f) == 16}
/// Returns `true` if proposition is correct, `false` otherwise.
pub fn prove5<F: Fn(u64, u64, u64, u64, u64) -> u64>(f: F) -> bool {count5(f) == 32}
/// Returns `true` if proposition is correct, `false` otherwise.
pub fn prove6<F: Fn(u64, u64, u64, u64, u64, u64) -> u64>(f: F) -> bool {count6(f) == 64}
/// Returns `true` if proposition is correct, `false` otherwise.
pub fn prove7<F: Fn(u64, u64, u64, u64, u64, u64, u64) -> u64>(f: F) -> bool {count7(f) == 128}
/// Returns `true` if proposition is correct, `false` otherwise.
pub fn prove8<F: Fn(u64, u64, u64, u64, u64, u64, u64, u64) -> u64>(f: F) -> bool {
    count8(f) == 256
}
/// Returns `true` if proposition is correct, `false` otherwise.
pub fn prove9<F: Fn(u64, u64, u64, u64, u64, u64, u64, u64, u64) -> u64>(f: F) -> bool {
    count9(f) == 512
}
/// Returns `true` if proposition is correct, `false` otherwise.
pub fn prove10<F: Fn(u64, u64, u64, u64, u64, u64, u64, u64, u64, u64) -> u64>(f: F) -> bool {
    count10(f) == 1024
}

/// Returns `T` if `a` is `true`, `F` otherwise.
/// In logical terminology this corresponds to a proposition.
pub fn prop(a: bool) -> u64 {if a {T} else {F}}

pub fn false_1(_: u64) -> u64 {0}
pub fn not(a: u64) -> u64 {!a}
pub fn id(a: u64) -> u64 {a}
pub fn true_1(_: u64) -> u64 {T}

pub fn false_2(_: u64, _: u64) -> u64 {0}
pub fn and(a: u64, b: u64) -> u64 {a & b}
pub fn or(a: u64, b: u64) -> u64 {a | b}
pub fn xor(a: u64, b: u64) -> u64 {a ^ b}
pub fn eq(a: u64, b: u64) -> u64 {!(a ^ b)}
pub fn imply(a: u64, b: u64) -> u64 {!a | b}
pub fn true_2(_: u64, _: u64) -> u64 {T}

pub fn false_3(_: u64, _: u64, _: u64) -> u64 {0}
pub fn false_4(_: u64, _: u64, _: u64, _: u64) -> u64 {0}
pub fn false_5(_: u64, _: u64, _: u64, _: u64, _: u64) -> u64 {0}
pub fn false_6(_: u64, _: u64, _: u64, _: u64, _: u64, _: u64) -> u64 {0}

pub fn and3(a: u64, b: u64, c: u64) -> u64 {and(and(a, b), c)}
pub fn and4(a: u64, b: u64, c: u64, d: u64) -> u64 {and(and(a, b), and(c, d))}
pub fn and5(a: u64, b: u64, c: u64, d: u64, e: u64) -> u64 {and(and(a, b), and3(c, d, e))}
pub fn and6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64) -> u64 {
    and(and3(a, b, c), and3(d, e, f))
}
pub fn and7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64) -> u64 {
    and(and4(a, b, c, d), and3(e, f, g))
}
pub fn and8(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64) -> u64 {
    and(and4(a, b, c, d), and4(e, f, g, h))
}
pub fn and9(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, i: u64) -> u64 {
    and(and5(a, b, c, d, e), and4(f, g, h, i))
}
pub fn and10(
    a: u64, b: u64, c: u64, d: u64, e: u64,
    f: u64, g: u64, h: u64, i: u64, j: u64
) -> u64 {
    and(and5(a, b, c, d, e), and5(f, g, h, i, j))
}

pub fn or3(a: u64, b: u64, c: u64) -> u64 {or(or(a, b), c)}
pub fn or4(a: u64, b: u64, c: u64, d: u64) -> u64 {or(or(a, b), or(c, d))}
pub fn or5(a: u64, b: u64, c: u64, d: u64, e: u64) -> u64 {or(or3(a, b, c), or(d, e))}
pub fn or6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64) -> u64 {or(or3(a, b, c), or3(d, e, f))}
pub fn or7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64) -> u64 {
    or(or4(a, b, c, d), or3(e, f, g))
}
pub fn or8(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64) -> u64 {
    or(or4(a, b, c, d), or4(e, f, g, h))
}
pub fn or9(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, i: u64) -> u64 {
    or(or5(a, b, c, d, e), or4(f, g, h, i))
}
pub fn or10(
    a: u64, b: u64, c: u64, d: u64, e: u64,
    f: u64, g: u64, h: u64, i: u64, j: u64
) -> u64 {
    or(or5(a, b, c, d, e), or5(f, g, h, i, j))
}

pub fn xor3(a: u64, b: u64, c: u64) -> u64 {xor(xor(a, b), c)}
pub fn xor4(a: u64, b: u64, c: u64, d: u64) -> u64 {xor(xor(a, b), xor(c, d))}
pub fn xor5(a: u64, b: u64, c: u64, d: u64, e: u64) -> u64 {xor(xor3(a, b, c), xor(d, e))}
pub fn xor6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64) -> u64 {
    xor(xor3(a, b, c), xor3(d, e, f))
}
pub fn xor7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64) -> u64 {
    xor(xor4(a, b, c, d), xor3(e, f, g))
}
pub fn xor8(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64) -> u64 {
    xor(xor4(a, b, c, d), xor4(e, f, g, h))
}
pub fn xor9(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, i: u64) -> u64 {
    xor(xor5(a, b, c, d, e), xor4(f, g, h, i))
}
pub fn xor10(
    a: u64, b: u64, c: u64, d: u64, e: u64,
    f: u64, g: u64, h: u64, i: u64, j: u64
) -> u64 {
    xor(xor5(a, b, c, d, e), xor5(f, g, h, i, j))
}

pub fn imply3(a: u64, b: u64, c: u64) -> u64 {and(imply(a, b), imply(b, c))}
pub fn imply4(a: u64, b: u64, c: u64, d: u64) -> u64 {
    and3(imply(a, b), imply(b, c), imply(c, d))
}
pub fn imply5(a: u64, b: u64, c: u64, d: u64, e: u64) -> u64 {
    and4(imply(a, b), imply(b, c), imply(c, d), imply(d, e))
}
pub fn imply6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64) -> u64 {
    and5(imply(a, b), imply(b, c), imply(c, d), imply(d, e), imply(e, f))
}
pub fn imply7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64) -> u64 {
    and6(imply(a, b), imply(b, c), imply(c, d), imply(d, e), imply(e, f), imply(f, g))
}
pub fn imply8(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64) -> u64 {
    and7(imply(a, b), imply(b, c), imply(c, d), imply(d, e), imply(e, f), imply(f, g), imply(g, h))
}
pub fn imply9(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, i: u64) -> u64 {
    and8(imply(a, b), imply(b, c), imply(c, d), imply(d, e),
         imply(e, f), imply(f, g), imply(g, h), imply(h, i))
}
pub fn imply10(
    a: u64, b: u64, c: u64, d: u64, e: u64,
    f: u64, g: u64, h: u64, i: u64, j: u64,
) -> u64 {
    and9(imply(a, b), imply(b, c), imply(c, d), imply(d, e),
         imply(e, f), imply(f, g), imply(g, h), imply(h, i), imply(i, j))
}

pub type Pred1 = fn(u64) -> u64;
pub type Pred2 = fn(u64, u64) -> u64;

pub trait Enumerable: Sized {
    fn start() -> Self;
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
        assert_eq!(count1(false_1), 0);
        assert_eq!(count1(not), 1);
        assert_eq!(count1(id), 1);
        assert_eq!(count1(true_1), 2);

        assert_eq!(count2(false_2), 0);
        assert_eq!(count2(and), 1);
        assert_eq!(count2(xor), 2);
        assert_eq!(count2(eq), 2);
        assert_eq!(count2(or), 3);
        assert_eq!(count2(true_2), 4);
        assert_eq!(count2(imply), 3);
        assert_eq!(count2(|a, b| imply(and(a, b), or(a, b))), 4);

        assert_eq!(count3(|a, b, c| and(or(a, b), and(a, c))), 2);
        assert_eq!(count4(|a, b, c, d| and(or(a, b), or(c, d))), 9);
        assert_eq!(count5(|_, _, _, _, _| T), 32);
        assert_eq!(count6(|_, _, _, _, _, _| T), 64);
        assert_eq!(count7(|_, _, _, _, _, _, _| T), 128);
        assert_eq!(count8(|_, _, _, _, _, _, _, _| T), 256);
        assert_eq!(count9(|_, _, _, _, _, _, _, _, _| T), 512);
        assert_eq!(count10(|_, _, _, _, _, _, _, _, _, _| T), 1024);
    }
}

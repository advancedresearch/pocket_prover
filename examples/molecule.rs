#![allow(non_snake_case)]

use pocket_prover::*;

fn main() {
    println!("Water: {}", measure(100, || prove!(&mut |H, O, a, b, c| {
        imply(
            water(H, O, a, b, c),
            eq(q(a, b), q(b, c))
        )
    })));

    println!("Salt: {}", measure(100, || prove!(&mut |Na, Cl, a, b| {
        imply(
            salt(Na, Cl, a, b),
            atom(b, Cl)
        )
    })));

    println!("Oxygen: {}", measure(100, || prove!(&mut |O, Bond2, a, b| {
        imply(
            oxygen(O, Bond2, a, b),
            bond(a, b, Bond2)
        )
    })));
}

pub fn atom(a: u64, atom: u64) -> u64 {eq(q(a, a), atom)}
pub fn bond(a: u64, b: u64, bond: u64) -> u64 {and(eq(a, b), eq(q(a, b), bond))}
pub fn react2(a: [u64; 2], b: [u64; 2]) -> u64 {
    and!(
        xor!(
            and(
                eq(a[0], b[0]),
                eq(a[1], b[1])
            )
        )
    )
}

pub fn water(H: u64, O: u64, a: u64, b: u64, c: u64) -> u64 {
    and!(
        atom(a, H),
        atom(b, O),
        atom(c, H),
        eq(a, b),
        eq(b, c),
    )
}

pub fn salt(Na: u64, Cl: u64, a: u64, b: u64) -> u64 {
    and!(
        atom(a, Na),
        atom(b, Cl),
        eq(a, b)
    )
}

pub fn methane(H: u64, C: u64, a: u64, b: [u64; 4]) -> u64 {
    and!(
        atom(a, C),
        atom(b[0], H),
        atom(b[1], H),
        atom(b[2], H),
        atom(b[3], H),
        eq(a, b[0]),
        eq(a, b[1]),
        eq(a, b[2]),
        eq(a, b[3]),
    )
}

pub fn oxygen(O: u64, E2: u64, a: u64, b: u64) -> u64 {
    and!(
        atom(a, O),
        atom(b, O),
        bond(a, b, E2),
        eq(a, b),
    )
}

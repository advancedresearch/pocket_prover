#![feature(slice_patterns)]

extern crate pocket_prover;

use pocket_prover::*;

#[allow(unused_variables)]
fn main() {
    println!("Result {}", proven(33, &mut |vs| {
        if let &[a, b, c, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z,
                 aa, ab, ac, ad, ae, af, ag, ah] = vs {
            imply(
                xorn(&[a, f, i, p, ab, ae, p, q, r, ae]),
                imply(a, not(ae))
            )
        } else {F}
    }));
}

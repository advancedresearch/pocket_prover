extern crate pocket_prover;

use pocket_prover::*;

fn main() {
    println!("This example will take roughly 4 min 30 sec to run on a laptop.");
    println!("Normally, this proof would require 18 446 744 073 709 552 000 cases.");
    println!("That's roughly 18 447 *quadrillions*, now reduced to 150 323 855 294 cases.");
    println!("{}", path1_proven(64, &mut |f, x| {
        imply(
            and3(
                imply(f[0], x[0]),
                imply(f[1], eq(x[0], x[1])),
                eq(f[0], f[1])
            ),
            eq(x[0], x[1])
        )
    }));
}

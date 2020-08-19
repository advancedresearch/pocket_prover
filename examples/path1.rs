extern crate pocket_prover;

use pocket_prover::*;

fn main() {
    println!("=== Path Semantical Logic ===");
    println!("The notation `f(x)` means `x` is uniquely associated with `f`.");
    println!("For more information, see the section 'Path Semantical Logic' in documentation.");
    println!("");

    print!("(f(x), g(y), h(z), f=g ⊻ f=h) => (x=y ∨ x=z): ");
    println!("{}\n", path1_prove!(&mut |(f, g, h), (x, y, z)| {
        imply(
            and4(
                imply(f, x),
                imply(g, y),
                imply(h, z),
                xor(eq(f, g), eq(f, h))
            ),
            or(eq(x, y), eq(x, z))
        )
    }));

    print!("(f(x), g(y), f=g => h, h(z)) => (x=y => z): ");
    println!("{}\n", path1_prove6(&mut |(f, g, h), (x, y, z)| {
        imply(
            and4(
                imply(f, x),
                imply(g, y),
                imply(eq(f, g), h),
                imply(h, z)
            ),
            imply(eq(x, y), z)
        )
    }));
}

use pocket_prover::*;

fn main() {
    println!("This example shows how to extract data from a theory.");
    println!("");
    println!("When you have many assumptions, it can be difficult to see patterns.");
    println!("However, there is technique that lets you bring a pattern into focus.");
    println!("");
    println!("First, you decide which expressions you want to focus on.");
    println!("Using these expressions, a truth table will be extracted.");
    println!("");
    println!("For example, in a theory: (a = b) ∧ c");
    println!("I choose to focus on `a ∧ c` and `b ∧ c`");
    println!("");
    println!("(a ∧ c) (b ∧ c) (∃)");
    println_extract!(
        &mut |a, b, c| and(eq(a, b), c);
        x0 => and(a, c),
        x1 => and(b, c),
    );

    println!("");
    println!("By looking at the table above one can see that `a ∧ c` and `b ∧ c` are equal.");
    println!("Therefore, one can prove:");
    println!("");
    println!("   (a = b) ∧ c");
    println!("-----------------");
    println!("(a ∧ c) = (b ∧ c)");
    println!("");
    println!("Result: {}", prove!(&mut |a, b, c| {
        imply(
            and(eq(a, b), c),
            eq(and(a, c), and(b, c))
        )
    }));
}

extern crate pocket_prover;

use pocket_prover::*;

fn main() {
    println!("Example taken from:\nhttp://www.inf.ed.ac.uk/teaching/courses/dmmr/slides/13-14/Ch1c.pdf");
    println!("");
    println!("This example demonstrates a proof technique to reduce");
    println!("quantifiers in first-order logic to propositional logic.");
    println!("");
    println!("C(x) = x in this class");
    println!("B(x) = x has read the book");
    println!("P(x) = x passed the first exam");
    println!("");
    println!("∃x(C(x) ∧ ¬B(x)) = somebody in this class has not read the book");
    println!("∀x(C(x) -> P(x)) = everyone in this class passed the first exam");
    println!("----------------");
    println!("∃x(P(x) ∧ ¬B(x)) = somebody who passed the first exam has not read the book");
    println!("");
    println!("In the 'quantifier' example, when working with predicates you need");
    println!("example predicates to test the proofs.");
    println!("");
    println!("Here we use a different technique:");
    println!(" - Replace the quantifier `∃x(p(x))` with an implication `x -> p`");
    println!(" - Remove the quantifier `∀x(p(x))` by lifting up predicate to proposition `p`");
    println!("");
    println!("This allows us to check the proof without providing example predicates");
    println!("");
    println!("Somebody passed the exam without reading the book: {}",
        prove4(&mut |c, b, p, x| {
            imply(
                and(
                    // ∃x(C(x) ∧ ¬B(x))
                    imply(x, and(c, not(b))),
                    // ∀x(C(x) -> P(x))
                    imply(c, p),
                ),
                // ∃x(P(x) ∧ ¬B(x))
                imply(x, and(p, not(b)))
            )
        }));
}

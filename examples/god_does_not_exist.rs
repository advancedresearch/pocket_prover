extern crate pocket_prover;

use pocket_prover::*;

fn main() {
    println!("REMEMBER TO TEST ASSUMPTIONS BY CHECKING ALL PROVABLE STATEMENTS");
    println!("");
    println!("This example shows why you should become an logical assumptionist.");
    println!("An logical assumptionist only accepts a proof in general as argument when");
    println!("every provable statement from the assumptions are acceptable,");
    println!("not just a reasonable sounding argument.");
    println!("");
    println!("If you want to troll someone that are not logical assumptionists,");
    println!("show them this:");
    println!("");
    println!("(God_exists -> good) ∧ (good ¬= evil) ∧ evil");
    println!("--------------------------------------------");
    println!("¬God_exists");
    println!("Result {}", prove3(|
        god,
        good,
        evil
    | {
        imply(
            and3(
                imply(god, good),
                not(eq(good, evil)),
                evil
            ),
            not(god)
        )
    }));
    println!("");
    println!("The problem with the assumptions above is that you can also prove");
    println!("there is no good.");
    println!("(God_exists -> good) ∧ (good ¬= evil) ∧ evil");
    println!("--------------------------------------------");
    println!("¬good");
    println!("Result {}", prove3(|
        god,
        good,
        evil
    | {
        imply(
            and3(
                imply(god, good),
                not(eq(good, evil)),
                evil
            ),
            not(good)
        )
    }));
    println!("");
    println!("Regardless of whether you believe a god exists or not,");
    println!("it is hard to believe that no good exists.");
    println!("Therefore, there must be something wrong with assumptions.");
    println!("");
    println!("The problem is actually that `(¬∃ P) = (∀ ¬P)` instead of a simple inverse.");
    println!("An updated proof clears up the ambiguity:");
    println!("");
    println!("(God_exists -> all_good) ∧ (all_good ¬= evil_exists) ∧ evil_exists");
    println!("= ¬God_exists ∧ ¬all_good ∧ evil_exists");
    println!("Result {}", prove3(|
        god,
        good,
        evil
    | {
        eq(
            and3(
                imply(god, good),
                not(eq(good, evil)),
                evil
            ),
            and3(not(god), not(good), evil)
        )
    }));
    println!("");
    println!("Now you have some assumptions that can be discussed.");
    println!("");
    println!("One more thing about logical assumptionists:");
    println!("There is no problem accepting this proof regardless of religious beliefs,");
    println!("because assumptions are clearly defined and have no obvious wrong conclusions.");
    println!("The point with the proof is not to show that you are correct,");
    println!("but what follows from the assumptions and then improve them!");
}

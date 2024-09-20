use pocket_prover::*;

fn main() {
    let n = 100;

    // true
    println!("Sesh: {}", measure(n, || prove!(&mut |a| {
        eq(not(qu(a)), qu(not(a)))
    })));

    // false
    println!("Platonic Sesh: {}", measure(n, || prove!(&mut |a| {
        eq(not(pqu(a)), pqu(not(a)))
    })));

    // false
    println!("Platonic Eq Not: {}", measure(n, || prove!(&mut |a| {
        eq(pqu(a), pqu(not(a)))
    })));

    // true
    println!("Composite Sesh: {}", measure(n, || prove!(&mut |a| {
        eq(not(re_sesh(pqu(a))), re_sesh(pqu(not(a))))
    })));

    // true
    println!("Eq: {}", measure(n, || prove!(&mut |a| {
        eq(re_sesh(pqu(a)), qu(a))
    })));

    // true
    println!("Sesh Id: {}", measure(n, || prove!(&mut |a| {
        eq(re_sesh(un_sesh(a)), a)
    })));

    // true
    println!("Sesh Inv Id: {}", measure(n, || prove!(&mut |a| {
        eq(un_sesh(re_sesh(a)), a)
    })));

    // false
    println!("Sesh Un-Qu-Re: {}", measure(n, || prove!(&mut |a| {
        eq(re_sesh(qubit(un_sesh(a))), qubit(a))
    })));

    // false
    println!("Sesh Re: {}", measure(n, || prove!(&mut |a| {
        eq(re_sesh(a), a)
    })));

    // false
    println!("Sesh Re == Un: {}", measure(n, || prove!(&mut |a| {
        eq(re_sesh(a), un_sesh(a))
    })));
}

#[macro_use]
extern crate pocket_prover_derive;
extern crate pocket_prover;

use pocket_prover::Construct;

#[derive(Construct)]
pub struct Foo {
    pub a: u64,
    pub b: u64,
}

#[derive(Construct)]
pub struct Bar<T = ()> {
    pub foo: T,
    pub a: u64,
    pub b: u64,
}

#[test]
fn foo_a_b() {
    let vs = &[1, 2];
    let foo: Foo = Construct::construct(vs);
    assert_eq!(foo.a, 1);
    assert_eq!(foo.b, 2);
}

#[test]
fn bar_a_b() {
    let vs = &[1, 2];
    let bar: Bar = Construct::construct(vs);
    assert_eq!(bar.a, 1);
    assert_eq!(bar.b, 2);
}

#[test]
fn bar_foo_a_b() {
    let vs = &[1, 2, 3, 4];
    let bar: Bar<Foo> = Construct::construct(vs);
    assert_eq!(bar.foo.a, 1);
    assert_eq!(bar.foo.b, 2);
    assert_eq!(bar.a, 3);
    assert_eq!(bar.b, 4);
}

#[test]
fn bar_bar_foo_a_b() {
    let vs = &[1, 2, 3, 4, 5, 6];
    let bar: Bar<Bar<Foo>> = Construct::construct(vs);
    assert_eq!(bar.foo.foo.a, 1);
    assert_eq!(bar.foo.foo.b, 2);
    assert_eq!(bar.foo.a, 3);
    assert_eq!(bar.foo.b, 4);
    assert_eq!(bar.a, 5);
    assert_eq!(bar.b, 6);
}

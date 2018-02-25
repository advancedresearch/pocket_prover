# pocket_prover-derive

Derive procedural macros for `pocket_prover`.

Example:

```ignore
#[macro_use]
extern crate pocket_prover_derive;
extern crate pocket_prover;

use pocket_prover::Construct;

#[derive(Construct)]
pub struct Foo {
    pub a: u64,
    pub b: u64,
}
```

Since `pocket_prover` uses only `u64`,
it is the only valid concrete field type.

The macro supports generic arguments, assuming that
the inner type implements `Construct`:

```ignore
#[derive(Construct)]
pub struct Bar<T = ()> {
    pub foo: T,
    pub a: u64,
    pub b: u64,
}
```

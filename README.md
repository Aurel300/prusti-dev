# Prusti Closures

*Prusti Closures* is the tool accompanying the OOPSLA'21 submission #215 *"Modular Specification and Verification of Closures in Rust"*. It extends the Rust verifier [Prusti](http://prusti.org) with additional specification and verification capabilities for reasoning about common usages of [Rust closures](https://doc.rust-lang.org/book/ch13-01-closures.html).

## Running the closure tests

To reproduce our experiments from the paper, start the Docker image and run the following:
```
./all-closure-tests.py
```
The above script runs Prusti Closures on all examples listed in the paper and a few more (22 in total). After "starting benchmark...", the script prints, for each successfully analysed example, its name and its runtime in seconds. For examples starting with `pass/`, we check that Prusti Closures successfully verifies the provided specification. For examples starting with `fail/` (which correspond to examples ending with `_err` in the paper), we check that Prusti Closures reports an error at the location marked with `ERROR` in the example.

Everything should be in order if the script produces no error messages.

An example of the output resulting from a successful run is given below (runtimes may vary depending on the underlying machine).
```
starting benchmark...
1 runs per case
17 positive cases
5 negative cases

pass/closures/all.rs,9.5989210359985
pass/closures/any.rs,9.854438432957977
pass/closures/basic.rs,6.75475998793263
pass/closures/blameassgn.rs,4.746646519983187
pass/closures/call-desc.rs,6.141880391049199
pass/closures/counter.rs,5.408806488034315
pass/closures/delegation.rs,5.736118012922816
pass/closures/ghost_pred.rs,4.300891521968879
pass/closures/invariant.rs,4.864901955006644
pass/closures/map_vec.rs,11.506163846002892
pass/closures/option.rs,26.600703014060855
pass/closures/outer.rs,4.70862147200387
pass/closures/repeat_with_n.rs,12.287058002897538
pass/closures/result_uoe.rs,6.379525606986135
pass/closures/thesis-1.rs,4.878504915046506
pass/closures/types.rs,9.329049038002267
pass/closures/views.rs,5.537902040989138
fail/closures/any.rs,10.038811897975393
fail/closures/basic.rs,4.143177651916631
fail/closures/blameassgn.rs,5.228910960024223
fail/closures/counter.rs,4.951890297001228
fail/closures/option_map.rs,7.974158967961557
```

Table 1 in our paper contains one additional example (marked with #) that is handcrafted and analysed via a separate script; it can be reproduced by running [Silicon](https://github.com/viperproject/silicon/) on the file:
```
path/to/silicon/silicon.sh prusti-tests/tests/verify/pass/closures/fold_list_rev.sil
```
The expected outcome should look as follows (runtimes may vary):
```
Silicon 1.1-SNAPSHOT (3cab9bae+@(detached))
Silicon finished verification successfully in 5.17s.
```

## Specification syntax

Our paper contains idealised syntax for closure specifications in which we use mathematical notation to improve readability. Our implementation builds upon Prusti, which, in turn, builds upon the Rust compiler. We needed to adapt our idealised syntax to deal with restrictions imposed by the Rust compiler. For example, we need additional annotations for extracting argument types.

We give two examples with explanatory comments to illustrate the specification syntax supported by our implementation:

```rust 
// full example: /prusti-tests/tests/verify/pass/closures/counter.rs

// specification entailment (see Sect. 3.3 in the paper) assigning a spec to a closure argument
// note that cl_result is used to refer to the result of a closure call in specification
// entailments and call descriptions to disambiguate it from the result of the annotated
// method (here, the method "foo")
#[requires(f |= || -> i32 [ requires(true), ensures(cl_result >= 2) ])]
fn foo<T: FnMut() -> i32>(f: T) {}

fn main() {
    let mut x = 0;
    let mut inc = closure!( // closures with specifications need to be
                            // wrapped in the closure! macro
        #[view(x: i32)] // every captured variable and its type 
                        // needs to be declared using the #[view()] attribute
        #[invariant(*views.x >= 0)] // single state invariant
        #[invariant(old(*views.x) <= *views.x)] // history invariant (see Sect. 3.2)
        #[requires(true)] // precondition (see Sect. 3.1)
        #[ensures(old(*views.x) + 1 == *views.x)] // two-state postcondition (see Sect. 3.1)
        #[ensures(result == old(*views.x))] // postcondition, result refers to the returned value
        || -> i32 { let r = x; x += 1; r } // the actual closure
    );

    inc();
    inc();
    foo(inc);
}
```

```rust 
// full example: prusti-tests/tests/verify/pass/closures/repeast_with_n.rs

#[requires(f |= || -> i32 [ requires(true), ensures(true) ])] // specification entailment (see Sect 3.3)
#[requires(n >= 0)] // precondition
#[ensures(vec_len(&result) == n)] // postcondition
#[ensures( // postcondition with call description (see Sect. 3.4)
    forall(|idx: usize| 0 <= idx && idx < vec_len(&result)
        ==> (f ~> || -> i32 {} { cl_result == vec_lookup(&result, idx) }))
)]
fn repeat_with_n<F: FnMut() -> i32>(mut f: F, n: usize) -> Vec<i32> {
    // ...
}
```


### Deviations in syntax

The following list summarises all differences between the syntax supported by our tool and the syntax proposed in our paper:

- Annotations that are required by our implementation but are not needed in our idealised syntax:
    - Every closure with specifications must be wrapped in a `closure!(...)` macro call. Within the parentheses, zero or more Rust attributes (e.g. `#[requires(...)]`) are expected, followed by the closure itself.
    - Closures in `closure!(...)` macros must be annotated with their argument types and return type. This is optional in normal Rust code.
    - Any captured variable used within closure specifications must be declared using a `#[view(varname: vartype)]` annotation, where:
      - `varname` is the name of the variable; and
      - `vartype` is the Rust type of the variable.
    - Within specifications, views are referred to using `*views.varname`; our idealized syntax allows directly referring to variables by their captured name
- Specification entailments (see Sect. 3.3 in the paper) have a syntax of the form: `f |= |args...| -> T [ assertions... ]` (or `f |=! ...`), where:
  - `f` is the closure instance;
  - `args...` is a list of argument variables with type annotations;
  - `T` is the return type of the closure (omitted if the return type is `()`); and
  - `assertions...` is a list of assertions in the form `requires(...)` or `ensures(...)`.
- Call descriptions (see Sect. 3.4 in the paper) have a syntax of the form: `f ~> |args...| -> T { prestate } { poststate }`, where:
  - `f` is the closure instance;
  - `args...` is a list of argument variables with type annotations;
  - `T` is the return type of the closure (omitted if the return type is `()`);
  - `prestate` is an assertion that must hold before the call; and
  - `poststate` is an assertion that must hold after the call.
- All arguments in a call description are assumed to be universally quantified (expressed with the colon syntax in the paper); arguments can be constrained to be equal to other variables or constants with appropriate assertions in the prestate.
- Call descriptions in the form `f ~> ...` express that `f` itself is universally quantified (colon syntax in the paper), whereas `f ~>! ...` indicates it is not.
- `outer(...)` (Sect. 3.4) is not used in the examples, as it is not necessary to clarify which state we refer to in call descriptions and specification entailments in our examples.
- `cl_result` is available in the poststate of call descriptions and the postconditions of specification entailments to refer to the value returned by the closure, whereas `result` refers to the value returned by the higher-order function itself.

# License

Prusti Closures is licensed under the Mozilla Public License Version 2.0 (http://www.mozilla.org/MPL/2.0/).

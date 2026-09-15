Revise primitive effects

We're working in a new version of the F* compiler where the effect system has
already been vastly simplified.

Currently, we have the following primitive effects:

- PURE, GHOST, DIV, TAC, ML

Each effect is indexed by a precondition (pre:prop), a result type (a:Type), and a postcondition (post:a -> prop)

The effect `Tot a` is a special case of `PURE a True (fun _ -> True)`, etc.

I want to simplify things further, and make the core of F* even simpler.

In the main syntax of the compiler, FStarC.Syntax.Syntax, I want to simplify
things so that an computation type is just:

* An effect label and a result type

The primitive effects are

* Tot a, Ghost a, Div a, Tac a, and ML a

The front end syntax should still allow defining effect abbreviations with pre
and postconditions, but these should be desugared away

For instance:

* Pure a pre post

is desugared to

* #pre -> Tot (x:a{post x})

I.e., 

* the precondition becomes an implicit prop-typed argument, requiring the caller to supply a proof
* the postcondition becomes a refinement on the result type

Lemma is a special case, because one can just write `Lemma (ensures post)`, but this is just sugar for `#True -> Ghost (_:unit{post})`

This change will propagate throughout the compiler, but it will simplify many
things and rule out various sources of bugs, e.g., where arrow types are
compared without considering the pre/post conditions on their computation types
in the RHS

There should still be a way to define user-defined effect labels, as is
currently supported, but those user-defined effects will also be just a label
and a type, i.e., `E a`.

### Type inference

The major source of risk with this plan is that it will impact type inference.

There will be parts of the code currently like this:

```
let f () : Pure int (requires True) (ensures fun x -> x > 17) = 18
let test (y:int) = f() == y
```

Where the equality in `test` typechecks at type `eq2 #int`

But, with this proposed change, if we're not careful, it may fail to typecheck
if type inference picks `eq2 #(x:int{x>17})`

### Extraction

A concern, though a lesser one, is that this will also impact the extraction
ABI, adding an extra unit argument to functions that are desugared.

This extra arugment acceptable, but if it proves to be a problem, one might
consider moving the refinement to the last argument. 

E.g., the desugaring of `t -> Pure s pre post` could be `x:t{pre} -> Tot (y:s{post s})`

This desugaring, if it works, may even be preferable, but it may also have an
impact on the previous risk, i.e., on type inference with refinements.

### Other simplifications

Recent commits have special handling for expected types and postconditions, in
support of better error localization. We will no longer have any special
handling for postconditions. Read the commit history, and PR.md for this recent
work, including a failed experiment.


# Summary

Do detailed research in the codebase and make a plan.

I want to port the entire compiler to this new, simpler representation, and get
back to a state where the entire CI gate passes.
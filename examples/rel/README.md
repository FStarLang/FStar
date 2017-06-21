
# Examples for A Monadic Framework for Relational Verification (Functional Pearl)

All the examples are in the `rel` subdir, but some use things in
`dm4free` internally. This is known to work with the
`c_relational-ci_r3` branch of F*, commit bc4d52178 in particular.

## Section 1

- `Loops.fst`: `sum_up`/`sum_dn` from 1.1

## Section 2

- `Loops.fst`: `sum_up`/`sum_dn` from 2.4

## Section 3

- `Swap.fst`: all the program transformations on commands from 3.2

## Section 4

- `OneTimePad.fst`: the RANDOM monad from 4.1 and one-time pad from 4.2

## Section 5

- `IfcRulesReify.fst`: the IFC type system from 5.1
- `IfcTypechecker.fst`: the IFC typecheckers from 5.1 and 5.2
- `IfcExampleReify2.fst`: the simple program from 5.2 and its hybrid proof
- `IfcDelimitedRelease.fst`: the delimited release definition from 5.3
- `IfcDeclassify.fst`: the simple definition of when declassification from 5.3

## Section 6

- `Memo.fst`: the memoization example from 6.1
- `UnionFind.fst`: the union find example from 6.2

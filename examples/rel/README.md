
# Examples for A Monadic Framework for Relational Verification

All the examples are in the `rel` subdir, but some use things in
`dm4free` internally. This is known to work with the
`c_relational-ci_r3` branch of F*, commit 380997df in particular.
This requires Z3 version 4.5.1 to verify
(in particular `IfcMonitor` is known to fail with Z3 4.5.0).

## Section 1

- `Loops.fst`: `sum_up`/`sum_dn` from 1.1

## Section 2

- `Loops.fst`: `sum_up`/`sum_dn` from 2.4

## Section 3

- `Swap.fst`: all the program transformations on commands from 3.2

- `Benton2004.fst`, `Benton2004.RHL.fst` and
  `Benton2004.RHL.Examples2.fst`: relational Hoare logic by Benton
  (2004), model, soundness proofs and examples as described in 3.3
  (other files `Benton2004.*` model the rest of Benton's paper)

## Section 4

- `IfcRulesReify.fst`: the IFC type system from 4.1
- `IfcMonitor.fst` and `IfcMonitorTest.fst`: the dynamic IFC monitor from 4.2
- `IfcTypechecker.fst`: the IFC typecheckers from 4.1 and 4.3
- `IfcExampleReify2.fst`: the simple program from 4.3 and its hybrid proof
- `IfcDelimitedRelease.fst`: the delimited release definition from 4.4
- `IfcDeclassify.fst`: the simple definition of when declassification from 4.4

## Section 5

- `../dm4free/FStar.DM4F.Heap.Random.fst`,`../dm4free/FStar.DM4F.Random.fst`:
  definition of the RAND effect in 5.1 and proof of `mass_leq` lemma in 5.2
- `OTP.fst`: proof of perfect secrecy of one-time pad in 5.2
- `../dm4free/FStar.DM4F.OTP.Heap.fst`,`../dm4free/FStar.DM4F.OTP.Random.fst`:
  the variant of the RAND effect in 5.1 used in the proof in 5.3
- `ElGamal.fst`: the proof of the secrecy lemma in 5.3

## Section 6

- `Memo.fst`: the memoization example from 6.1
- `UnionFind.fst`: the union find example from 6.2

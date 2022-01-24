# SteelCore Supplementary Material

This material contains the mechanized proofs for the model presented in the SteelCore paper.
More precisely, we implement here a version of our effectul CSL semantics complete with monotonic state, non-determinism and pre- and post-conditions.

All the development is done within the F* proof assistant, which relies on the Z3 theorem prover
for semi-automated proofs. In order to verify the code, you will need to typecheck the source files
using a development version of F* that can be obtained on
[the project repository](https://github.com/FStarLang/FStar). Please use the snapshot corresponding
to the commit ??? and follow the "Building F* from sources" section of `INSTALL.md` to build the
typechecker.

Please refer to the Figure 1. of the paper for the dependency between modules. F*, similarly to OCaml,
distinguishes between interface files (`.fsti`) and implementation files (`.fst`). For each module
name mentioned later, you can look at the corresponding implementation and/or interface file.

The various pragmas introduced by `#` are used to pass certain options controlling the SMT encoding
and the behavior of Z3.

## Auxiliary proofs shown in the paper

You can find all the code presented in section 2 of the paper in the `MParIndex` module and check
that the proofs typecheck without any additional annotations.

## Organization of the main SteelCore developement

The core semantics using indexed effectful action trees presented in Section 3, together with
their soundess proof, are available in `Steel.Semantics.Hoare.MST`. They build upon the `MST`
and `NMST` modules, which provide a model of monotonic state as described by Ahman et al.

`Steel.PCM` encodes partially commutative monoids into F*, and is used by `Steel.PCM.Memory`
whose goal is to show a proof of concept of a generic memory model depending on an abstract PCM.
As stated by the paper, the rest of our implementation currently relies on a different memory
model that is specialized for the fractional permission PCM.

`Steel.Memory` and `Steel.Actions` define the SteelCore program logic presented in Section 4,
but specialized for the fractional permission PCM. `Steel.Memory` provides the definition of
our separation logic and its connectives, as well as our model of memory as a map from abstract
addresses to heap cells. `Steel.Actions` defines our stored invariants, as well as a variety
of standard actions.

`Steel.Semantics.Instantiate` then builds upon them to instantiate the State Typeclass
presented in section 3.0. `Steel.Memory.Tactics` instantiates the F* canonical monoid tactic
with our separation logic terms to automate frame resolution.

`Steel.Effect` and `Steel.Effect.Atomic` build upon the SteelCore program logic defined in
`Steel.Memory` and `Steel.Actions` to define two monadic effects, encapsulating respectively
non-atomic and atomic computations.

These effects are then used to define the interface of the SteelCore Program Logic, in the form of a
set of libraries:
* `Steel.HigherReference` and `Steel.Reference` deal with memory references, storing respectively
  values of types contained in universe 1 and 0;
* `Steel.SteelAtomic.Basics` contains helper functions for programming in the
  `SteelAtomic` effect;
* `Steel.SteelT.Basics` contains helper functions for programming in a simplified version of the
   `Steel` effect where pre- and post- conditions are trivial.

Using these libraries, we present the implementation of the examples from section 5:
* `Steel.SpinLock` is the spinlock using CAS of 5.1;
* `Steel.Primitive.ForkJoin` is the fork/join parallelism structure of 5.2;
* `Steel.Channel.*` is the implementation of the simplex channels protocols of 5.3.

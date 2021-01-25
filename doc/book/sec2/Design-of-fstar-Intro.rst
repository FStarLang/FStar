.. _Design-of-fstar-Intro:

The Design of F*
================

Proving and programming are inextricably linked, especially in
dependent type theory, where constructive proofs are just
programs. However, not all programs are proofs. Effective programmers
routinely go beyond a language of pure, total functions and use
features like non-termination, state, exceptions, and IO---features
that one does not usually expect in proofs. Thus, while languages like
Coq and Agda are functional programming languages, one does not
typically use them for general-purpose programming---that they are
implemented in OCaml and Haskell is a case in point. Lean4, another
type-theory-based proof assistant *is* implemented in Lean, but
effectful programs are not usually proven correct in Lean.

Outside dependent type theory, verification-oriented languages like
Dafny and WhyML provide good support for effects and semi-automated
proving via SMT solvers, but have logics that are much less powerful
than Coq, Agda, and Lean, and only limited support (if at all) for
higher-order programming.

F* aims to spans the capabilities of interactive proof assistants like
Coq and Agda, general-purpose programming languages like OCaml and
Haskell, and SMT-backed semi-automated program verification tools like
Dafny and WhyML. It provides the expressive power of a logic like
Coq's, but with a richer, effectful dynamic semantics. It also
provides the flexibility to mix SMT-based automation with dependently
typed proof terms (like Agda) or tactic-based interactive proofs like
Coq or Lean. And it supports idiomatic higher-order, effectful
programming with the predictable, call-by-value cost model of OCaml,
but with the encapsulation of effects provided by Haskell.

.. toctree::
   :hidden:
   :maxdepth: 1
   :caption: Contents:

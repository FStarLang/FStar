.. _Part5:

########################################
Tactics and Metaprogramming with Meta-F*
########################################

**This part of the book is still heavily under construction**

So far, we have mostly relied on the SMT solver to do proofs in F*.
This works rather well: we got this far, after all! However, sometimes,
the SMT solver is really not able to complete our proof, or takes too
long to do so, or is not *robust* (i.e. works or fails due to seemingly
insignificant changes).

This is what Meta-F* was originally designed for. It provides the
programmer with more control on how to break down a proof and guide
the SMT solver towards finding a proof by using *tactics*. Moreover, a
proof can be fully completed within Meta-F* without using the SMT
solver at all. This is the usual approach taken in other proof
assistants (such as Lean, Coq, or Agda), but it's not the preferred
route in F*: we will use the SMT for the things it can do well, and
mostly write tactics to "preprocess" obligations and make them easier
for the solver, thus reducing manual effort.

Meta-F* also allows for *metaprogramming*, i.e. generating programs
(or types, or proofs, ...) automatically. This should not be
surprising to anyone already familiar with proof assistants and the
`Curry-Howard correspondence
<https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence>`_. There
are however some slight differences between tactic-based proofs and
metaprogramming, and more so in F*, so we will first look at
automating proofs (i.e. tactics), and then turn to metaprogramming
(though we use the generic name "metaprogram" for tactics as well).

In summary, when the SMT solver "just works" we usually do not bother
writing tactics, but, if not, we still have the ability to roll up our
sleeves and write explicit proofs.

Speaking of rolling up our sleeves, let us do just that, and get our
first taste of tactics.

.. toctree::
   :maxdepth: 1
   :caption: Contents:

   part5_meta

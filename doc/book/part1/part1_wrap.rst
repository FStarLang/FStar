.. _Part1_wrap:

Wrapping up
===========

Congratulations! You've reached the end of an introduction to basic F*.

You should have learned the following main concepts:

* Basic functional programming
* Using types to write precise specifications
* Writing proofs as total functions
* Defining and working with new inductive types
* Lemmas and proofs by induction

Throughout, we saw how F*'s use of an SMT solver can reduce the
overhead of producing proofs, and you should know enough now to
be productive in small but non-trivial F* developments.

However, it would be wrong to conclude that SMT-backed proofs in F*
are all plain sailing. And there's a lot more to F* than SMT
proofs---so read on through the rest of this book.

But, if you do plan to forge ahead with mainly SMT-backed proofs, you
should keep the following in mind before attempting more challenging
projects.

It'll serve you well to learn a bit more about how an SMT solver works
and how F* interfaces with it---this is covered in a few upcoming
sections, including a section on :ref:`classical proofs
<Part2_connectives>`.

* In particular, when trying to use universally quantified hypotheses
  or when proving existentially quantified goals, you will need to
  learn a bit about `E-matching and quantifier patterns
  <https://github.com/FStarLang/FStar/wiki/Quantifiers-and-patterns>`_. This
  will take some investment, but learning how to use them effectively
  can significantly reduce the complexity of proofs in the long run.

* If you're interested in doing proofs about arithmetic, particularly
  nonlinear arithmetic, then before diving in, you would do well to
  read more about the F* library ``FStar.Math.Lemmas`` and F*
  arithmetic settings.

* `Profiling and debugging failed proofs <https://github.com/FStarLang/FStar/wiki/Profiling-Z3-queries>`_.

* `Replaying proofs using unsat cores <https://github.com/FStarLang/FStar/wiki/Robust,-replayable-proofs-using-unsat-cores,-(aka,-hints,-or-how-to-replay-verification-in-milliseconds-instead-of-minutes)>`_

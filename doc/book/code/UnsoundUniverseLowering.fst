module UnsoundUniverseLowering

(*** INTENTIONALLY UNSOUND ***)

/// This assumed interface provides intentionally unsound
/// axioms to lower the universe of a type.
///
/// It can be convenient to use this for experiments that require
/// impredicativity, (e.g., those that demonstrate paradoxes) though
/// it is clearly unsound and not recommended for use in code or
/// proofs that really matter

/// A type constructor in universe 0

//SNIPPET_START: lower$
assume
val lower ([@@@strictly_positive] a:Type u#a) : Type u#0
//SNIPPET_END: lower$

/// A function to inject a value in universe `a`
/// to a value in `lower a`
//SNIPPET_START: inject$
assume
val inject (#a:Type u#a) (x:a) : lower a
//SNIPPET_END: inject$

/// This is the main axiom here:
///   -- From a value in universe 0, (x:lower a)
///      we can extract a value in universe a
assume
//SNIPPET_START: project$
val project (#a:Type u#a) (x:lower a) : a

assume
val inj_proj (#a:Type u#a) (x:a)
  : Lemma (project (inject x) == x)
//SNIPPET_END: project$


assume
val proj_inj (#a:Type u#a) (x:lower a)
  : Lemma (inject (project x) == x)




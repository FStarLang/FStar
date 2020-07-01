module FStar.Unsound.UniverseLowering

(*** INTENTIONALLY UNSOUND ***)

/// This assumed interface provides intentionally unsound
/// axioms to lower the universe of a type.
///
/// It can be convenient to use this for experiments that require
/// impredicativity, though it is clearly unsound and not recommended
/// for use in code or proofs that really matter

/// A type constructor in universe 0
val lower (a:Type u#a) : Type u#0

/// A function to inject a value in universe `a`
/// to a value in `lower a`
val inject (#a:Type u#a) (x:a) : Tot (lower a)

/// This is the main axiom here:
///   -- From a value in universe 0, (x:lower a)
///      we can extract a value in universe a
val project (#a:Type u#a) (x:lower a) : Tot a

/// And these properties tells that us that project/inject are inverses
val inj_proj (#a:Type u#a) (x:a)
  : Lemma (project (inject x) == x)
          [SMTPat (inject x)]

val proj_inj (#a:Type u#a) (x:lower a)
  : Lemma (inject (project x) == x)
          [SMTPat (project x)]

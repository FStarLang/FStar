(*
   Computation types must be INVARIANT under an EQ constraint.

   Before specifications were moved out of `comp_typ`, `solve_eq` in
   src/typechecker/FStarC.TypeChecker.Rel.fst discharged an EQ problem between
   two computation types with the *one-directional* subsumption guard

       (pre2 ==> pre1) /\ (pre2 ==> forall x. post1 x ==> post2 x)

   But EQ is exactly what F* uses for INVARIANT positions: the arguments of a
   type application are related with EQ because all type constructors are
   invariant.  Relating specifications by mere implication there made every type
   constructor covariant in the specifications it mentions, so a computation
   type occurring negatively could be silently widened -- which proves False and
   produces runtime type errors.

   A computation type no longer carries a specification: a precondition is a
   trailing implicit `squash` binder and a postcondition is a refinement on the
   result type, so both are part of the *type* and are related structurally.
   Every `expect_failure` below is therefore rejected for the ordinary reason
   that two different types are not equal.

   tests/micro-benchmarks/Subsumption.fst exercises the SUB direction; this file
   is the EQ coverage.
*)
module SimpleEffects_CompEqInvariance

type restrictive = x:int -> Pure int (requires x > 0) (ensures fun r -> r == x /\ r > 0)
type permissive  = x:int -> Pure int (requires True)  (ensures fun r -> r == x /\ r > 0)

/// A completely abstract type constructor is enough: `f` is a variable, so
/// nothing but invariance can justify this.
[@@ expect_failure]
let cast (f : Type -> Type) (x : f permissive) : f restrictive = x

/// The same widening through a type abbreviation, using `Lemma` -- the most
/// common specification form.
let neg (a:Type) : Type = a -> squash False

let nc : neg (unit -> Lemma False) = fun g -> g ()

[@@ expect_failure]
let widen_lemma : neg (unit -> Lemma True) = nc

/// Postconditions alone (no preconditions) suffice.
assume val np_post : neg (unit -> Pure int (requires True) (ensures fun r -> r == 0))
[@@ expect_failure]
let widen_post : neg (unit -> Pure int (requires True) (ensures fun _ -> True)) = np_post

/// ... and through a user-defined inductive, which turns the widening into a
/// closed proof of False with no `admit`, no `assume` and no warning.
noeq type negi (a:Type) = | N : (a -> squash False) -> negi a

let npi : negi permissive = N (fun (f:permissive) -> let _ = f (-1) in ())

[@@ expect_failure]
let widen_inductive : negi restrictive = npi

/// Runtime consequence: a `restrictive` function is invoked outside its
/// precondition and a refinement-typed value is populated with a witness that
/// violates the refinement.  `observed` is statically proved `> 0` but the
/// extracted program prints -1.
noeq type negr (a:Type) = | R : (a -> y:int{y > 0}) -> negr a

let npr : negr permissive = R (fun (f:permissive) -> f (-1))

[@@ expect_failure]
let widen_runtime : negr restrictive = npr

/// --- Directions that MUST keep working / keep being rejected ---

/// Sound contravariance: `Lemma False <: Lemma True`, so
/// `neg (unit -> Lemma True) <: neg (unit -> Lemma False)`.
assume val nt : neg (unit -> Lemma True)
let narrow_is_fine : neg (unit -> Lemma False) = nt

/// Control: the analogous widening for refinement types is already rejected,
/// which isolates the defect to computation types rather than to variance in
/// general.
assume val nref : neg (x:int{x > 0})
[@@ expect_failure]
let widen_refinement : neg int = nref

/// Control: plain computation *subsumption* (relation SUB, not EQ) is sound and
/// must keep working -- `permissive` has the weaker precondition.  The two
/// arrows differ in arity, because `restrictive` takes a trailing implicit
/// `squash` binder for its precondition and `permissive` does not, so relating
/// them takes an eta-expansion; subtyping performs it (see
/// [try_eta_expand_to_expected_typ] in src/typechecker/FStarC.TypeChecker.Util.fst),
/// so writing it by hand is not required.
let bare_arrow_subsumption_direct (p:permissive) : restrictive = p

let bare_arrow_subsumption (p:permissive) : restrictive = fun x -> p x

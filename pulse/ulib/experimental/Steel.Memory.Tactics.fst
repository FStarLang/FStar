module Steel.Memory.Tactics

module M = Steel.Memory

open FStar.Algebra.CommMonoid.Equiv
open FStar.Tactics
open FStar.Tactics.CanonCommMonoidSimple.Equiv

let equiv_refl (x:M.hprop) : Lemma (M.equiv x x) = ()

let equiv_sym (x y:M.hprop) : Lemma
  (requires M.equiv x y)
  (ensures M.equiv y x)
  = ()

let equiv_trans (x y z:M.hprop) : Lemma
  (requires M.equiv x y /\ M.equiv y z)
  (ensures M.equiv x z)
  = ()

inline_for_extraction noextract let req : equiv M.hprop =
  EQ M.equiv
     equiv_refl
     equiv_sym
     equiv_trans

let cm_identity (x:M.hprop) : Lemma ((M.emp `M.star` x) `M.equiv` x)
  = M.star_commutative x M.emp;
    M.emp_unit x

inline_for_extraction noextract let rm : cm M.hprop req =
  CM M.emp
     M.star
     cm_identity
     M.star_associative
     M.star_commutative
     M.star_congruence

inline_for_extraction noextract let canon () : Tac unit =
  canon_monoid (`req) (`rm)

let can_be_split_into (outer inner delta:M.hprop) =
  outer `M.equiv` (inner `M.star` delta)

inline_for_extraction noextract let resolve_frame () : Tac unit =
  dump "enter resolve_frame";
  refine_intro();
  flip();
  dump "pre canon";
  canon()

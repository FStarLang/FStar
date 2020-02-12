module Steel.Memory.Tactics

module M = Steel.Memory

/// Attribute for normalization
let __reduce__ = ()

unfold
let normal (#a:Type) (x:a) =
  let open FStar.Algebra.CommMonoid.Equiv in
  norm [delta_attr [`%__reduce__];
       delta;
        delta_only [
          `%__proj__CM__item__mult;
          `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
          `%fst; `%snd];
        primops; iota; zeta] x

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

[@__reduce__]
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
  (inner `M.star` delta) `M.equiv` outer

let squash_and p q (x:squash (p /\ q)) : (p /\ q) =
  let x : squash (p `c_and` q) = FStar.Squash.join_squash x in
  x


inline_for_extraction noextract let resolve_frame () : Tac unit =
  norm [delta_attr [`%__reduce__];
       delta;
        delta_only [
          `%__proj__CM__item__mult;
          `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
          `%fst; `%snd];
        primops; iota; zeta];
  refine_intro();
  flip();
  apply_lemma (`unfold_with_tactic);
  split();
  norm [delta_only [`%can_be_split_into]];
  canon();
  trivial()

inline_for_extraction noextract let reprove_frame () : Tac unit =
  norm [delta_attr [`%__reduce__];
       delta;
        delta_only [
          `%__proj__CM__item__mult;
          `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
          `%fst; `%snd];
        primops; iota; zeta];
  apply (`squash_and);
  norm [delta_only [`%can_be_split_into]];
  split();
  canon();
  trivial()

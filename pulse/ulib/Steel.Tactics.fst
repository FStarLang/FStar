module Steel.Tactics

open FStar.HyperStack.ST
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

open LowStar.Array
open Steel.Resource


(* Generic framing operation for RSTATE (through resource inclusion) *)

let frame_delta_pre (outer0 inner0 delta:resource) =
  outer0 `can_be_split_into` (inner0,delta)

let frame_delta_post (#a:Type) (outer1 inner1:a -> resource) (delta:resource) =
  forall x. (outer1 x) `can_be_split_into` (inner1 x,delta)

let frame_delta (outer0:resource)
                (inner0:resource)
                (#a:Type)
                (outer1:a -> resource)
                (inner1:a -> resource)
                (delta:resource) =
    frame_delta_pre outer0 inner0 delta /\
    frame_delta_post outer1 inner1 delta


open FStar.Algebra.CommMonoid.Equiv
open FStar.Tactics
open FStar.Tactics.CanonCommMonoidSimple.Equiv

inline_for_extraction noextract let req : equiv resource =
  EQ equal
     equal_refl
     equal_symm
     equal_trans

inline_for_extraction noextract let rm : cm resource req =
  CM empty_resource
     (<*>)
     equal_comm_monoid_left_unit
     equal_comm_monoid_associativity
     equal_comm_monoid_commutativity
     equal_comm_monoid_cong

let squash_and p q (x:squash (p /\ q)) : (p /\ q) =
  let x : squash (p `c_and` q) = FStar.Squash.join_squash x in
  x

inline_for_extraction noextract let resolve_frame_delta () : Tac unit =
  norm [delta_only [`%frame_delta]];
  apply (`squash_and);
  split ();
  norm [delta_only [`%frame_delta_pre]];
  apply_lemma (quote can_be_split_into_star);
  canon_monoid req rm;
  norm [delta_only [`%frame_delta_post]];
  ignore (forall_intro ());
  apply_lemma (quote can_be_split_into_star);
  canon_monoid req rm

inline_for_extraction noextract let resolve_delta () : Tac unit =
  refine_intro ();
  flip ();
  apply_lemma (`unfold_with_tactic);
  norm [delta_only [`%frame_delta]];
  split ();
  norm [delta_only [`%frame_delta_pre]];
  apply_lemma (quote can_be_split_into_star);
  flip ();
  canon_monoid req rm;
  norm [delta_only [`%frame_delta_post]];
  ignore (forall_intro ());
  apply_lemma (quote can_be_split_into_star);
  canon_monoid req rm

inline_for_extraction noextract let resolve_split () : Tac unit =
  apply_lemma (quote can_be_split_into_star);
  canon_monoid req rm

inline_for_extraction noextract let resolve_res_eq () : Tac unit =
  refine_intro ();
  flip ();
  canon_monoid req rm

(**** Tactics unit testing *)

assume val r1 : resource
assume val r2 : resource
assume val r3 : resource
assume val r4 : resource
assume val r5 : resource

let _ =
  assert_by_tactic ((r1 <*> r2) `can_be_split_into` (r1, r2)) resolve_split

let assert_delta_equal
  (outer: resource)
  (inner: resource)
  (delta: resource)
  : Lemma
    (requires (with_tactic resolve_split (squash (outer `can_be_split_into` (inner, delta)))))
    (ensures (True))
  = ()

let _ =
  assert_delta_equal (r1 <*> r2) r1 r2

let _ =
  assert_delta_equal (r1 <*> r2 <*> r3 <*> r4 <*> r5) (r2 <*> r4) (r1 <*> r3 <*> r5)

[@expect_failure]
let _ =
  assert_delta_equal (r1 <*> r2 <*> r3 <*> r4 <*> r5) (r2 <*> r4) (r1 <*> r5)

let _ =
  assert_delta_equal (r1 <*> ((r2 <*> r3) <*> r4) <*> r5) (r4 <*> r2) (r3 <*> r1 <*> r5)

let _ =
  assert_delta_equal (r1 <*> ((r2 <*> r3) <*> r4 <*> r5)) (r2 <*> r4) ((r1 <*> r3) <*> r5)

let _ =
  assert_delta_equal ((r1 <*> r2) <*> (r3 <*> r4 <*> r5)) (r2 <*> r4) (r1 <*> (r3 <*> r5))

let _ =
  assert_delta_equal (r1 <*> (r2 <*> r3) <*> (r4 <*> r5)) (r2 <*> r4) (r1 <*> r3 <*> r5)

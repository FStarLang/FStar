module LowStar.RST.Tactics

open FStar.HyperStack.ST
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

// open FStar.ModifiesGen
open LowStar.Array
open LowStar.Resource


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
  
let unfold_with_tactic (t:unit -> Tac 'a) (p:Type)
  : Lemma (requires p)
          (ensures (with_tactic t p))
  = admit()

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

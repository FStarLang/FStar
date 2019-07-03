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


inline_for_extraction noextract let resolve_frame_delta' () : Tac unit =
  split ();
  dump "4";
  norm [delta_only [`%frame_delta_pre]];
  dump "5";
  apply_lemma (quote can_be_split_into_star);
  dump "6";
  flip ();
  dump "7";
  canon_monoid req rm;
  dump "8";
  norm [delta_only [`%frame_delta_post]];
  dump "9";
  ignore (forall_intro ());
  dump "10";
  apply_lemma (quote can_be_split_into_star);
  dump "11";
  canon_monoid req rm;
  dump "12"

let squash_and p q (x:squash (p /\ q)) : (p /\ q) =
  let x : squash (p `c_and` q) = FStar.Squash.join_squash x in
  x

inline_for_extraction noextract let resolve_frame_delta () : Tac unit =
  dump "Second phase: 1";
  norm [delta_only [`%frame_delta]];
  dump "Second phase: 2";
  apply (`squash_and);
  resolve_frame_delta' ()

let unfold_with_tactic (t:unit -> Tac 'a) (p:Type)
  : Lemma (requires p)
          (ensures (with_tactic t p))
  = admit()


let foobar () : Tac unit =
  dump "A";
  refine_intro ();
  dump "B";
  flip ();
  dump "C";
  apply_lemma (`unfold_with_tactic);
  dump "D";
  exact (`0)

let l_True_term : l_True = ()

let baz () : Tac unit =
  dump "Z";
  exact (`l_True_term)

assume val test (#[foobar()] x : int { FStar.Tactics.with_tactic baz True }) (y:bool) : unit

//let atest (p q: Type) =
//  let x : (p /\ q) = _ by (apply (`squash_and); dump "A"; tadmit()) in
//  ()

let run () =
    test true

inline_for_extraction noextract let resolve_delta () : Tac unit =
  dump "1";
  refine_intro ();
  dump "2";
  flip ();
  dump "3";
  apply_lemma (`unfold_with_tactic);
  dump "3.1";
  norm [delta_only [`%frame_delta]];
  dump "3.2";
  resolve_frame_delta' ()
  // split ();
  // dump "4";
  // norm [delta_only [`%frame_delta_pre]];
  // dump "5";
  // apply_lemma (quote can_be_split_into_star);
  // dump "6";
  // flip ();
  // dump "7";
  // canon_monoid req rm;
  // dump "8";
  // norm [delta_only [`%frame_delta_post]];
  // dump "9";
  // ignore (forall_intro ());
  // dump "10";
  // apply_lemma (quote can_be_split_into_star);
  // dump "11";
  // canon_monoid req rm;
  // dump "12"

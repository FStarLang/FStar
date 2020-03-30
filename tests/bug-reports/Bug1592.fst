module Bug1592

open FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer

(*
 * A pathological example for modifies_trans
 * Thanks to Santiago for the example
 *)
assume val f: b:buffer UInt8.t -> Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc_buffer b) h0 h1)

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 10"

let test (a:buffer UInt8.t) (b:buffer UInt8.t) : Stack unit
  (requires fun h0 -> live h0 a /\ live h0 b /\ disjoint a b)
  (ensures  fun h0 _ h1 -> live h1 a /\ live h1 b /\ modifies (loc_union (loc_buffer a) (loc_buffer b)) h0 h1)
= push_frame();
  let c = alloca 0uy 1ul in
  let d = alloca 0uy 1ul in
  f a;
  f b;
  f c;
  f d;
  f a;
  f b;
  f c;
  f d;
  pop_frame()

module ST = FStar.HyperStack.ST

(*
 * Example of linear modifies clauses in action
 *
 * This example illustrates how we expect modifies clauses to work for the common
 *   case of push_frame, allocte tmp, modify tmp + some other buffer, pop_frame.
 *   Since allocations are not observable to the caller, the final modifies clause just
 *   contains the other buffer.
 *
 * Below, F denotes the facts that are known at each point.
 * 
 * The comments just after the example outline the proof.
 *)
let example1 (b:buffer int)
  : ST unit (requires (fun h0      -> live h0 b /\ length b == 1))
            (ensures  (fun h0 _ h1 -> modifies (loc_buffer b) h0 h1))
  = let h0 = ST.get () in

    push_frame ();
    let h1 = ST.get () in

    // F1 : fresh_frame h0 h1
    // F2 : modifies loc_none h0 h1

    let tmp = alloca 0 1ul in
    let h2 = ST.get () in

    // F3 : fresh_loc (loc_buffer tmp) h1 h2
    // F4 : modifies loc_none h1 h2

    upd tmp 0ul 1;
    let h3 = ST.get () in

    // F5 : modifies (loc_buffer tmp) h2 h3

    upd b 0ul 1;
    let h4 = ST.get () in

    // F6 : modifies (loc_buffer b) h3 h4

    pop_frame ();
    let h5 = ST.get () in

    // F7 : popped h4 h5

    ()

(*
 * Our goal (from the postcondition) is to prove:
 *
 * G : modifies (loc_buffer b) h0 h5
 *
 * Triggered by the terms G and F1, lemma modifies_remove_fresh_frame fires, resulting in 2 new goals:
 *
 * G1 : HS.fresh_frame h0 h1
 * G2 : modifies (loc_union (loc_all_regions_from false (HS.get_tip h2)) (loc_buffer b)) h1 h5
 *
 * let l_goal = loc_union (loc_all_regions_from false (HS.get_tip h2)) (loc_buffer b)
 *
 * G1 is same as F1, that leaves G2
 *
 * Triggered by the terms F3, F4, and G2, lemma modifies_remove_new_loc fires, resulting in 4 new goals:
 *
 * G3 : fresh_loc (loc_buffer tmp) h1 h2
 * G4 : modifies loc_none h1 h2
 * G5 : l_goal `loc_includes` loc_none
 * G6 : modifies (loc_union loc_none l_goal) h2 h5
 *
 * G3 and G4 are same as F3 and F4, G5 is provable through lemma loc_includes_none, that leaves G6
 * We can simplify G6 to modifies l_goal h2 h5 (using lemma loc_union_loc_none_r)
 *
 * G6 : modifies l_goal h2 h5
 *
 * Triggered by the terms in F5 and G6, lemma modifies_trans_linear fires, resulting in 3 new goals:
 *
 * G7 : modifies (loc_buffer tmp) h2 h3
 * G8 : modifies l_goal h3 h5
 * G9 : l_goal `loc_includes` (loc_buffer tmp)
 *
 * G7 is same as F5, while G9 is provable from lemma loc_includes_region_buffer, that leaves G8
 *
 * Using one more such step of lemma modifies_trans_linear, and proving loc_includes using union elim lemmas,
 *   we get a new goal:
 *
 * G10 : modifies l_goal h4 h5
 *
 * Triggered by F7, lemma popped_modifies fires and gives us a new fact (postcondition):
 *
 * F8 : modifies (loc_region_only false (HS.get_tip h4)) h4 h5
 *
 * which is rewritten to (using the fact that HS.get_tip h4 == HS.get_tip h2):
 *
 * F9 : modifies (loc_region_only false (HS.get_tip h2)) h4 h5
 *
 * Now G10 can be proven with an application of modifies_trans_linear
 *)

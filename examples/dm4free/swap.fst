module Swap
open FStar.List.Tot
open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST
#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"

(** A relational example. Consider two functions f1 and f2, who read
    (resp. write) disjoint sets of references in the heap. Then, calling [f1
    (); f2 ()] should be the same as calling [f2 (); f1 ()]. *)

// Heap relies on sets with decidable equality... we follow suit.
module S = FStar.Set

// We reason about a set of addresses so as to reuse the [modifies] clause.
type addr_set = S.set nat

let disjoint (s1: addr_set) (s2: addr_set) =
  S.intersect s1 s2 == S.empty

(** [footprint f rs ws] means as long as two heaps coincide on [rs], then the
    resulting heaps coincide on [ws]. *)
let footprint (f: unit -> STNull unit) (rs: addr_set) (ws: addr_set) =
  forall (h_0 h_1: heap).
  let (), h'_0 = reify (f ()) h_0 in
  let (), h'_1 = reify (f ()) h_1 in
  modifies ws h_0 h'_0 /\ modifies ws h_1 h'_1 /\ (
  forall a. forall (r: ref a). S.mem (addr_of r) rs /\ (
    h_0 `contains_a_well_typed` r /\
    h_1 `contains_a_well_typed` r /\
    sel h_0 r == sel h_1 r
  ) ==> (
  forall a. forall (r: ref a). (
    S.mem (addr_of r) ws /\
    h'_0 `contains_a_well_typed` r /\
    h'_1 `contains_a_well_typed` r
  ) ==> sel h'_0 r == sel h'_1 r))

let swap (rs1: addr_set) (ws1: addr_set) (f1: unit -> STNull unit)
  (rs2: addr_set) (ws2: addr_set) (f2: unit -> STNull unit):
  Lemma
    (requires (disjoint ws1 ws2 /\ disjoint rs1 ws2 /\ disjoint rs2 ws2))
    (ensures (
      forall h_0. (
        let (), h_1 = reify (f1 ()) h_0 in
        let (), h'_1 = reify (f2 ()) h_1 in
        let (), h_2 = reify (f2 ()) h_0 in
        let (), h'_2 = reify (f1 ()) h_2 in
        forall r. (
        h_0 `contains_a_well_typed` r ==>
        sel h'_1 r == sel h'_2 r)))) =
  ()

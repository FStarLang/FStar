module Swap
open FStar.List.Tot
open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST
#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"

// Heap relies on sets with decidable equality... we follow suit.
module S = FStar.Set

// We reason about a set of addresses so as to reuse the [modifies] clause.
type addr_set = S.set nat

let heap_equiv_on (h_0:heap) (h_1:heap) (rs:addr_set) =
  forall (a:Type0). forall (r: ref a).
    S.mem (addr_of r) rs /\
    h_0 `contains` r /\
    h_1 `contains` r ==>
    sel h_0 r == sel h_1 r

let heap_eq (h:heap) (h_0:heap) (h_1:heap) =
   forall (a:Type) (r:ref a).  h `contains` r ==> sel h_0 r == sel h_1 r

(** [footprint f rs ws] means as long as two heaps coincide on [rs], then the
    resulting heaps coincide on [ws]. *)
let footprint (f: unit -> STNull unit) (rs: addr_set) (ws: addr_set) =
  forall (h_0: heap) (h_1: heap).{:pattern (reify (f ()) h_0);
                                    (reify (f ()) h_1)}
  let (), h'_0 = reify (f ()) h_0 in
  let (), h'_1 = reify (f ()) h_1 in
  modifies ws h_0 h'_0 /\
  modifies ws h_1 h'_1 /\
  (heap_equiv_on h_0 h_1 rs ==> heap_equiv_on h'_0 h'_1 ws)

(** A relational example. Consider two functions f1 and f2, who read
    (resp. write) disjoint sets of references in the heap. Then, calling [f1
    (); f2 ()] should be the same as calling [f2 (); f1 ()]. *)
val swap (rs1: addr_set) (ws1: addr_set) (f1: unit -> STNull unit)
  (rs2: addr_set) (ws2: addr_set) (f2: unit -> STNull unit)
  (h_0: heap) :
  Lemma
    (requires (S.disjoint ws1 ws2 /\ S.disjoint rs1 ws2 /\ S.disjoint rs2 ws1 /\
      footprint f1 rs1 ws1 /\ footprint f2 rs2 ws2))
    (ensures (
      let (), h_1 = reify (f1 ()) h_0 in
      let (), h'_1 = reify (f2 ()) h_1 in
      let (), h_2 = reify (f2 ()) h_0 in
      let (), h'_2 = reify (f1 ()) h_2 in
      heap_eq h_0 h'_1 h'_2))
let swap rs1 ws1 f1 rs2 ws2 f2 h_0 =
  let (), h_1 = reify (f1 ()) h_0 in //Strange that we seem to need these to trigger
  let (), h_2 = reify (f2 ()) h_0 in //the same terms in the post-condition don't seem to be sufficient
  ()                              //Also strange that the other two terms don't seem necessary


(** If whatever [f] writes only depends on [rs], then calling a [f] a second
    time should write the same values into the heap. *)
let idem (rs ws:addr_set) (f:unit -> STNull unit)  (h0:heap)
  : Lemma (requires (S.disjoint rs ws /\
                     footprint f rs ws))
          (ensures (let _, h1 = reify (f ()) h0 in
                    let _, h2 = reify (f ()) h1 in
                    heap_eq h0 h1 h2))
  = let _, h1 = reify (f ()) h0 in
    let _, h2 = reify (f ()) h1 in
    ()

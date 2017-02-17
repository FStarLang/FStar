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

// Apparently this lemma was missing from the Set library.
// JP: what would be a good SMTPat?
let disjoint_not_in_both s1 s2 x:
  Lemma
    (requires (disjoint s1 s2))
    (ensures (S.mem x s1 ==> ~(S.mem x s2)))
  [SMTPat (disjoint s1 s2)]
=
  if S.mem x s1 then begin
    if S.mem x s2 then begin
      S.mem_intersect x s1 s2;
      assert (S.intersect s1 s2 == S.empty);
      assert False
    end else
      ()
  end else
    ()

irreducible
let trigger #a (x: a) = True

(** [footprint f rs ws] means as long as two heaps coincide on [rs], then the
    resulting heaps coincide on [ws]. *)
let footprint (f: unit -> STNull unit) (rs: addr_set) (ws: addr_set) =
  // Note: just instantiating this quantifier yields useful modifies
  // clauses... hence the trigger.
  forall (h_0: heap). {:pattern (trigger h_0)}
  let (), h'_0 = reify (f ()) h_0 in
  modifies ws h_0 h'_0 /\ (
  forall (h_1: heap).
  let (), h'_1 = reify (f ()) h_1 in
  modifies ws h_1 h'_1 /\ (
  forall a. forall (r: ref a). S.mem (addr_of r) rs /\ (
    h_0 `contains_a_well_typed` r /\
    h_1 `contains_a_well_typed` r /\
    sel h_0 r == sel h_1 r
  ) ==> (
  forall a. forall (r: ref a). (
    S.mem (addr_of r) ws /\
    h'_0 `contains_a_well_typed` r /\
    h'_1 `contains_a_well_typed` r
  ) ==> sel h'_0 r == sel h'_1 r)))

val swap (rs1: addr_set) (ws1: addr_set) (f1: unit -> STNull unit)
  (rs2: addr_set) (ws2: addr_set) (f2: unit -> STNull unit)
  (h_0: heap) (a: Type) (r: ref a):
  Lemma
    (requires (disjoint ws1 ws2 /\ disjoint rs1 ws2 /\ disjoint rs2 ws1 /\
      footprint f1 rs1 ws1 /\ footprint f2 rs2 ws2 /\ h_0 `contains_a_well_typed` r))
    (ensures (
      let (), h_1 = reify (f1 ()) h_0 in
      let (), h'_1 = reify (f2 ()) h_1 in
      let (), h_2 = reify (f2 ()) h_0 in
      let (), h'_2 = reify (f1 ()) h_2 in
      sel h'_1 r == sel h'_2 r))
let swap rs1 ws1 f1 rs2 ws2 f2 h_0 a r =
  let (), h_1 = reify (f1 ()) h_0 in
  let (), h'_1 = reify (f2 ()) h_1 in
  let (), h_2 = reify (f2 ()) h_0 in
  let (), h'_2 = reify (f1 ()) h_2 in
  assert (trigger h_0);
  assert (modifies ws1 h_0 h_1);
  assert (modifies ws2 h_1 h'_1);
  assert (modifies ws2 h_0 h_2);
  assert (modifies ws1 h_2 h'_2);
  assert (forall a. forall (r: ref a). h_0 `contains_a_well_typed` r /\
    ~(S.mem (addr_of r) ws1) /\ ~(S.mem (addr_of r) ws2) ==>
    sel h_0 r == sel h_1 r /\ sel h_0 r == sel h_2 r /\
    sel h_0 r == sel h'_1 r /\ sel h_0 r == sel h'_2 r);
  assert (forall a. forall (r: ref a).
    S.mem (addr_of r) ws1 ==>
    ~(S.mem (addr_of r) ws2));
  assert (forall a. forall (r: ref a).
    S.mem (addr_of r) ws2 ==>
    ~(S.mem (addr_of r) ws1));
  assert (forall a. forall (r: ref a). h_0 `contains_a_well_typed` r /\
    S.mem (addr_of r) ws1 ==>
    sel h_0 r == sel h_2 r);
  assert (forall a. forall (r: ref a). h_0 `contains_a_well_typed` r /\
    S.mem (addr_of r) ws2 ==>
    sel h_0 r == sel h_1 r);
  assert (forall a. forall (r: ref a). h_0 `contains_a_well_typed` r /\
    S.mem (addr_of r) ws1 ==>
    sel h_1 r == sel h'_1 r);
  assert (forall a. forall (r: ref a). h_0 `contains_a_well_typed` r /\
    S.mem (addr_of r) ws2 ==>
    sel h_2 r == sel h'_2 r);

  match S.mem (addr_of r) ws1, S.mem (addr_of r) ws2 with
  | false, false ->
      ()
  | false, true ->
      admit ()
  | true, false ->
      assert (sel h_0 r == sel h_2 r);
      // JP: need to state that f1 and f2 preserve the "contains_a_well_typed"
      // property for any reference
      assert (forall a. forall (r: ref a). h_0 `contains_a_well_typed` r ==>
        h_2 `contains_a_well_typed` r);
      admit ()

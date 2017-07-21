module FStar.SnapshotHyperStack

open FStar.HyperHeap
open FStar.HyperStack

module HS = FStar.HyperStack
module HH = FStar.HyperHeap

type snapshot_heap = (HS.mem * option HS.mem)

let is_unrestricted (h : snapshot_heap) : bool =
Some? (snd h)

// The heap that is currently being modified.
let active_mem (m : snapshot_heap) : HS.mem =
match m with
| (h0, None) -> h0
| (h0, Some h1) -> h1

let equal_domains (h0 h1 : snapshot_heap) : Type =
HS.equal_domains (active_mem h0) (active_mem h1)

let lemma_equal_domains_trans (m0 m1 m2 : snapshot_heap) : Lemma
  (requires (equal_domains m0 m1 /\ equal_domains m1 m2))
  (ensures  (equal_domains m0 m2))
  [SMTPat (equal_domains m0 m1); SMTPat (equal_domains m1 m2)]
  = ()

let equal_stack_domains (h0 h1 : snapshot_heap) : Type =
HS.equal_stack_domains (active_mem h0) (active_mem h1)

let lemma_equal_stack_domains_trans (m0 m1 m2 : snapshot_heap) : Lemma
  (requires (equal_stack_domains m0 m1 /\ equal_stack_domains m1 m2))
  (ensures  (equal_stack_domains m0 m2))
  [SMTPat (equal_stack_domains m0 m1); SMTPat (equal_stack_domains m1 m2)]
  = ()

let heap (m:snapshot_heap) : hh =
(active_mem m).HS.h

let tip (m:snapshot_heap) : tip:rid {tip `HS.is_tip` (active_mem m).h} =
(active_mem m).HS.tip

// let am = active_mem m in am.tip

let fresh_frame (h0 h1 : snapshot_heap) : Type =
HS.fresh_frame (active_mem h0) (active_mem h1)

let poppable (h:snapshot_heap): Type =
HS.poppable (active_mem h)

let pop (h : snapshot_heap { poppable h}) : GTot snapshot_heap =
match h with
| (h0, None) -> (HS.pop h0, None)
| (h0, Some h1) ->
  let h2 = HS.pop h1 in
  (h0, Some h2)

let popped (h0 h1 : snapshot_heap) =
HS.popped (active_mem h0) (active_mem h1)

let upd (#a:Type) (m: snapshot_heap) (s:HS.reference a {HS.live_region (active_mem m) s.HS.id}) (v:a) : GTot snapshot_heap =
match m with
| (h0, None) -> (HS.upd h0 s v, None)
| (h0, Some h1) -> (h0, Some (HS.upd h1 s v))

let sel (#a:Type) (m: snapshot_heap) (s:reference a) : GTot a =
(active_mem m).h.[s.ref]

let contains (#a:Type) (m: snapshot_heap) (s: HS.reference a) =
HS.contains (active_mem m) s

let unused_in (#a:Type) (r:reference a) (h:snapshot_heap) =
  HS.unused_in r (active_mem h)

let modifies_one id h0 h1 = HS.modifies_one id (active_mem h0) (active_mem h1)
let modifies_ref (id:rid) (s:Set.set nat) (h0 h1 : snapshot_heap) =
  HS.modifies_ref id s (active_mem h0) (active_mem h1)

let lemma_upd_1 #a (h:snapshot_heap) (x:reference a) (v:a) : Lemma
   (requires (contains h x))
   (ensures (contains h x
             /\ modifies_one (frameOf x) h (upd h x v)
             /\ modifies_ref (frameOf x) (Set.singleton (as_addr x)) h (upd h x v)
             /\ sel (upd h x v) x == v ))
    [SMTPat (upd h x v); SMTPatT (contains h x)]
    = ()

let lemma_upd_2 (#a:Type) (h:snapshot_heap) (x:reference a) (v:a) : Lemma
   (requires (frameOf x = (tip h) /\ x `unused_in` h))
   (ensures (frameOf x = (tip h)
            /\ modifies_one (tip h) h (upd h x v)
            /\ modifies_ref (tip h) Set.empty h (upd h x v)
            /\ sel (upd h x v) x == v ))
    [SMTPat (upd h x v); SMTPatT (x `unused_in` h)]
    = ()

unfold let hs_remove_reference (#a:Type) (r:reference a) (m:mem{m `HS.contains` r /\ is_mm r}) :GTot mem =
  let h_0 = Map.sel m.h r.id in
  let h_1 = Heap.free_mm h_0 (HH.as_ref r.ref) in
  HS (Map.upd m.h r.id h_1) m.tip

let remove_reference (#a:Type) (r:HS.reference a) (m:snapshot_heap {m `contains` r /\ is_mm r}) : GTot snapshot_heap =
match m with
| (h0, None) -> (hs_remove_reference r h0, None)
| (h0, Some h1) -> (h0, Some (hs_remove_reference r h1))

let weak_contains (#a:Type) (m: snapshot_heap) (s: HS.reference a) =
  HS.weak_contains (active_mem m) s

let modifies (s : Set.set rid) (m0 m1 : snapshot_heap) =
  HS.modifies s (active_mem m0) (active_mem m1)

let modifies_transitively (s:Set.set rid) (m0 m1 : snapshot_heap) =
  HS.modifies_transitively s (active_mem m0) (active_mem m1)

let heap_only (m0:snapshot_heap) =
  HS.heap_only (active_mem m0)

module Pulse.Extrinsic.HeapLang.Nodes

(** Semantic implementation of node primitives, sharing the generic typed-cell
    bridge with integer operations. Each rule lifts a universal source-step
    characterization into AtomicLogic. Allocation constructs ownership for
    each permitted fresh address; field reads use contents uniqueness; link
    mutation preserves the original data component through the native write.
    Friend access to Proof is solely for typed/packed result conversion. *)
friend Pulse.Extrinsic.HeapLang.Proof

open Pulse.Extrinsic.HeapLang
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module M = Pulse.Extrinsic.HeapLang.Memory
module E = Pulse.Extrinsic.HeapLang.Semantics
module A = Pulse.Extrinsic.AtomicLogic
module R = Pulse.Extrinsic.Rules
module GS = Pulse.Lib.GhostSet

let atomic_new mask data next =
  let e = NewNode (Val data) (Val next) in
  let q = allocated data next in
  S.sep_laws ();
  A.lift E.language C.physical mask S.emp (E.Pack TRef e) (P.packed_post q) (fun f m ->
    C.physical_full m;
    E.node_allocation_steps data next (C.physical m);
    introduce forall e' s' spawned.
      E.packed_step (E.Pack TRef e) (C.physical m) e' s' spawned ==>
      A.result E.language C.physical mask (P.packed_post q) f m e' s' spawned
    with (
      introduce E.packed_step (E.Pack TRef e) (C.physical m) e' s' spawned ==>
        A.result E.language C.physical mask (P.packed_post q) f m e' s' spawned
      with (
        eliminate exists r. E.packed_to_val e' == Some (E.PackValue TRef r) /\
          spawned == [] /\ M.allocation_of (C.physical m) (data, next) r s'
        with (
          let after = C.allocate_memory_of mask (data, next) r s' f m in
          P.primitive_result mask q r f m after e' s' spawned
        ))))

let atomic_data mask r data next =
  let p = node r data next in
  let q = data_post r data next in
  let e = ReadData (Val r) in
  S.sep_laws ();
  A.lift E.language C.physical mask p (E.Pack TInt e) (P.packed_post q) (fun f m ->
    S.destruct_star_l p (S.star f (S.mem_invariant mask m)) m;
    C.points_to_contents_of r (data, next) m;
    E.node_data_atomic r data next (C.physical m);
    R.fact_emp (data == data);
    introduce forall e' s' spawned.
      E.packed_step (E.Pack TInt e) (C.physical m) e' s' spawned ==>
      A.result E.language C.physical mask (P.packed_post q) f m e' s' spawned
    with (
      if E.packed_step (E.Pack TInt e) (C.physical m) e' s' spawned then
        P.primitive_result mask q data f m m e' s' spawned
    ))

let atomic_next mask r data next =
  let p = node r data next in
  let q = next_post r data next in
  let e = ReadNext (Val r) in
  S.sep_laws ();
  A.lift E.language C.physical mask p (E.Pack TRef e) (P.packed_post q) (fun f m ->
    S.destruct_star_l p (S.star f (S.mem_invariant mask m)) m;
    C.points_to_contents_of r (data, next) m;
    E.node_next_atomic r data next (C.physical m);
    R.fact_emp (next == next);
    introduce forall e' s' spawned.
      E.packed_step (E.Pack TRef e) (C.physical m) e' s' spawned ==>
      A.result E.language C.physical mask (P.packed_post q) f m e' s' spawned
    with (
      if E.packed_step (E.Pack TRef e) (C.physical m) e' s' spawned then
        P.primitive_result mask q next f m m e' s' spawned
    ))

(** Observe the old pair before writing the new pair. Both the operational
    relation and postcondition retain data, so WriteNext cannot change it. *)
let atomic_write mask r data old next =
  S.sep_laws ();
  let p = node r data old in
  let q = P.constant_post #TUnit (node r data next) in
  let e = WriteNext (Val r) (Val next) in
  A.lift E.language C.physical mask p (E.Pack TUnit e) (P.packed_post q) (fun f m ->
    S.destruct_star_l p (S.star f (S.mem_invariant mask m)) m;
    C.points_to_contents_of r (data, old) m;
    let after = C.write_memory_of mask r (FStar.Ghost.hide (data, old)) (data, next) f m in
    E.node_write_atomic r data old next (C.physical m) (C.physical after);
    introduce forall e' s' spawned.
      E.packed_step (E.Pack TUnit e) (C.physical m) e' s' spawned ==>
      A.result E.language C.physical mask (P.packed_post q) f m e' s' spawned
    with (
      if E.packed_step (E.Pack TUnit e) (C.physical m) e' s' spawned then
        P.primitive_result mask q () f m after e' s' spawned
    ))

let new_node data next =
  atomic_new GS.empty data next;
  P.atomic_to_hoare S.emp (NewNode (Val data) (Val next)) (allocated data next)
let read_data r data next =
  atomic_data GS.empty r data next;
  P.atomic_to_hoare (node r data next) (ReadData (Val r)) (data_post r data next)
let read_next r data next =
  atomic_next GS.empty r data next;
  P.atomic_to_hoare (node r data next) (ReadNext (Val r)) (next_post r data next)
let write_next r data old next =
  atomic_write GS.empty r data old next;
  P.atomic_to_hoare (node r data old) (WriteNext (Val r) (Val next)) (P.constant_post (node r data next))
let exposed r data next = C.points_to_exposed_of r (data, next)

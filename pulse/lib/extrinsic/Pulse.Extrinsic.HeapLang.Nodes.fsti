module Pulse.Extrinsic.HeapLang.Nodes

open Pulse.Extrinsic.HeapLang
module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic

let node (r:H.core_ref) (data:int) (next:H.core_ref) = C.points_to_of r (data, next)
let allocated (data:int) (next r:H.core_ref) = node r data next
let data_post (r:H.core_ref) (data:int) (next:H.core_ref) (v:int) =
  S.star (node r data next) (S.pure (v == data))
let next_post (r:H.core_ref) (data:int) (next v:H.core_ref) =
  S.star (node r data next) (S.pure (v == next))

val atomic_new (mask:S.inames) (data:int) (next:H.core_ref)
  : Lemma (P.atomic mask S.emp (NewNode (Val data) (Val next)) (allocated data next))
val atomic_data (mask:S.inames) (r:H.core_ref) (data:int) (next:H.core_ref)
  : Lemma (P.atomic mask (node r data next) (ReadData (Val r)) (data_post r data next))
val atomic_next (mask:S.inames) (r:H.core_ref) (data:int) (next:H.core_ref)
  : Lemma (P.atomic mask (node r data next) (ReadNext (Val r)) (next_post r data next))
val atomic_write (mask:S.inames) (r:H.core_ref) (data:int) (old next:H.core_ref)
  : Lemma (P.atomic mask (node r data old) (WriteNext (Val r) (Val next))
      (P.constant_post (node r data next)))

val new_node (data:int) (next:H.core_ref)
  : Lemma (P.hoare S.emp (NewNode (Val data) (Val next)) (allocated data next))
val read_data (r:H.core_ref) (data:int) (next:H.core_ref)
  : Lemma (P.hoare (node r data next) (ReadData (Val r)) (data_post r data next))
val read_next (r:H.core_ref) (data:int) (next:H.core_ref)
  : Lemma (P.hoare (node r data next) (ReadNext (Val r)) (next_post r data next))
val write_next (r:H.core_ref) (data:int) (old next:H.core_ref)
  : Lemma (P.hoare (node r data old) (WriteNext (Val r) (Val next))
      (P.constant_post (node r data next)))
val exposed (r:H.core_ref) (data:int) (next:H.core_ref)
  : Lemma (S.implies (P.exposed (node r data next)) (node r data next))

module Pulse.Extrinsic.HeapLang.AtomicIncrement

open Pulse.Extrinsic.HeapLang
module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module U = Pulse.Extrinsic.HeapLang.AtomicUpdate
module GS = Pulse.Lib.GhostSet

let retry_at (#ctx:list ty) (r:expr ctx TRef) : expr (TInt :: ctx) TBool =
  If (Cas (rename (fun _ x -> There x) r) (Var Here) (Add (Var Here) (Val 1)))
    (Val false) (Val true)
let increment_at (#ctx:list ty) (r:expr ctx TRef) : expr ctx TUnit =
  While (Let (Load r) (retry_at r)) (Val ())
let increment (r:H.core_ref) = increment_at (Val #[] r)

let alpha (r:H.core_ref) (old:int) = C.points_to r old
let beta (r:H.core_ref) (old:int) (_:unit) = C.points_to r (old + 1)
let finished (result:S.slprop) (_:int) (_:unit) = result

val correct (r:H.core_ref) (inner:S.inames) (retry:S.slprop)
  (closing:int -> S.slprop) (result:S.slprop)
  : Lemma
      (requires U.protocol GS.empty inner retry (alpha r) (beta r) (finished result) closing)
      (ensures P.hoare retry (increment r) (P.constant_post result))

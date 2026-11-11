module Pulse.Extrinsic.HeapLang.AtomicIncrement

(** Source CAS increment and its abstract retry/abort/commit specification.
    The program repeatedly loads old, computes old+1, and attempts CAS;
    false means retry, true exits. It is multi-step, not a P.atomic expression.

    correct consumes a client-selected retry resource under AtomicUpdate's
    protocol. Each opening may choose a new old value: speculative loads
    abort, failed CAS attempts abort, and successful CAS commits old->old+1.
    Clients choose the closing resource and committed result without seeing
    this implementation's proof. Termination/lock-freedom is not asserted. *)

open Pulse.Extrinsic.HeapLang
open Pulse.Extrinsic.HeapLang.Notation
module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module U = Pulse.Extrinsic.HeapLang.AtomicUpdate
module GS = Pulse.Lib.GhostSet

let retry_at (#ctx:list ty) (r:expr ctx TRef) : expr (TInt :: ctx) TBool =
  let old = Var Here in
  if_ (cas (weaken r) old (add old (int_ 1))) (bool_ false) (bool_ true)
let increment_at (#ctx:list ty) (r:expr ctx TRef) : expr ctx TUnit =
  while_
    (let! old = load r in
     if_ (cas (weaken r) old (add old (int_ 1))) (bool_ false) (bool_ true))
    unit_
let increment (r:H.core_ref) = increment_at (Val #[] r)

let alpha (r:H.core_ref) (old:int) = C.points_to r old
let beta (r:H.core_ref) (old:int) (_:unit) = C.points_to r (old + 1)
let finished (result:S.slprop) (_:int) (_:unit) = result

val correct (r:H.core_ref) (inner:S.inames) (retry:S.slprop)
  (closing:int -> S.slprop) (result:S.slprop)
  : Lemma
      (requires U.protocol GS.empty inner retry (alpha r) (beta r) (finished result) closing)
      (ensures P.hoare retry (increment r) (P.constant_post result))

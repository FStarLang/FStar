module Pulse.Extrinsic.HeapLang.Stack

(** Header-based linked structure, with sequential source proofs.
    contents root xs owns a sentinel node (data 0) whose next field points to
    is_list head xs. Push reads that link, allocates a new head, and publishes
    it by updating the sentinel; peek follows the link and reads head data.
    The contracts preserve exact contents and all allocated ownership.

    Operations require exclusive structure ownership. LinkedConcurrent obtains
    it through a spinlock; these operations alone are not thread-safe or
    lock-free, and no reclamation is implemented. *)

open Pulse.Extrinsic.HeapLang
open Pulse.Extrinsic.HeapLang.Notation
module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module N = Pulse.Extrinsic.HeapLang.Nodes
module LL = Pulse.Extrinsic.HeapLang.List

let owned (root:H.core_ref) (xs:list int) (head:H.core_ref) =
  S.star (N.node root 0 head) (LL.is_list head xs)
let contents (root:H.core_ref) (xs:list int) = S.op_exists_Star (owned root xs)
let push_at (#ctx:list ty) (root:expr ctx TRef) (x:int) : expr ctx TUnit =
  let! head = next root in
  let root = weaken root in
  let! fresh = node (int_ x) head in
  link (weaken root) fresh
let peek_at (#ctx:list ty) (root:expr ctx TRef) : expr ctx TInt =
  let! head = next root in
  data head
let push (root:H.core_ref) (x:int) = push_at (Val #[] root) x
let peek (root:H.core_ref) = peek_at (Val #[] root)

val contents_intro (root head:H.core_ref) (xs:list int)
  : Lemma (S.implies (S.star (N.node root 0 head) (LL.is_list head xs)) (contents root xs))
val push_correct (root:H.core_ref) (x:int) (xs:list int)
  : Lemma (P.hoare (contents root xs) (push root x) (P.constant_post (contents root (x :: xs))))
val peek_correct (root:H.core_ref) (x:int) (xs:list int)
  : Lemma (P.hoare (contents root (x :: xs)) (peek root)
      (P.prepend_post (contents root (x :: xs)) (P.returns_value x)))
val exposed (root:H.core_ref) (xs:list int)
  : Lemma (S.implies (P.exposed (contents root xs)) (contents root xs))

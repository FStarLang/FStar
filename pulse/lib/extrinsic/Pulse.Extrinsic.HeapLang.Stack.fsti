module Pulse.Extrinsic.HeapLang.Stack

open Pulse.Extrinsic.HeapLang
module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module N = Pulse.Extrinsic.HeapLang.Nodes
module LL = Pulse.Extrinsic.HeapLang.List

let owned (root:H.core_ref) (xs:list int) (head:H.core_ref) =
  S.star (N.node root 0 head) (LL.is_list head xs)
let contents (root:H.core_ref) (xs:list int) = S.op_exists_Star (owned root xs)
let push_at (#ctx:list ty) (root:expr ctx TRef) (x:int) : expr ctx TUnit =
  Let (ReadNext root)
    (Let (NewNode (Val x) (Var Here))
      (WriteNext (rename (fun _ v -> There (There v)) root) (Var Here)))
let peek_at (#ctx:list ty) (root:expr ctx TRef) : expr ctx TInt =
  Let (ReadNext root) (ReadData (Var Here))
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

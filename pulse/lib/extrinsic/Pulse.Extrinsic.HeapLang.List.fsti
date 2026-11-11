module Pulse.Extrinsic.HeapLang.List

open Pulse.Extrinsic.HeapLang
module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module N = Pulse.Extrinsic.HeapLang.Nodes

let rec is_list (r:H.core_ref) (xs:list int) : Tot S.slprop (decreases xs) =
  match xs with
  | [] -> S.pure (r == H.core_ref_null)
  | x :: tail -> S.op_exists_Star (fun next -> S.star (N.node r x next) (is_list next tail))

let list_post (xs:list int) (r:H.core_ref) = is_list r xs
let next_post (r:H.core_ref) (x:int) (xs:list int) (next:H.core_ref) =
  S.star (N.node r x next) (is_list next xs)

val cons_intro (r:H.core_ref) (x:int) (next:H.core_ref) (xs:list int)
  : Lemma (S.implies (S.star (N.node r x next) (is_list next xs)) (is_list r (x :: xs)))
val cons_correct (x:int) (next:H.core_ref) (xs:list int)
  : Lemma (P.hoare (is_list next xs) (NewNode (Val x) (Val next))
      (list_post (x :: xs)))
val head_correct (r:H.core_ref) (x:int) (xs:list int)
  : Lemma (P.hoare (is_list r (x :: xs)) (ReadData (Val r))
      (P.prepend_post (is_list r (x :: xs)) (P.returns_value x)))
val next_correct (r:H.core_ref) (x:int) (xs:list int)
  : Lemma (P.hoare (is_list r (x :: xs)) (ReadNext (Val r))
      (next_post r x xs))
val exposed (r:H.core_ref) (xs:list int)
  : Lemma (S.implies (P.exposed (is_list r xs)) (is_list r xs))

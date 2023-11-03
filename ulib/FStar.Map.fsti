(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

(**

 @summary FStar.Map provides a polymorphic, partial map from keys to
   values, where keys support decidable equality.

 `m:Map.t key value` is a partial map from `key` to `value`

  A distinctive feature of the library is in its model of partiality.

  A map can be seen as a pair of:
    1. a total map `key -> Tot value`
    2. a set of keys that record the domain of the map

*)
module FStar.Map
module S = FStar.Set

(* Map.t key value: The main type provided by this module *)
val t (key:eqtype) ([@@@strictly_positive] value:Type u#a)
  : Type u#a

(* sel m k : Look up key `k` in map `m` *)
val sel: #key:eqtype -> #value:Type -> t key value -> key -> Tot value

(* upd m k v : A map identical to `m` except mapping `k` to `v` *)
val upd: #key:eqtype -> #value:Type -> t key value -> key -> value -> Tot (t key value)

(* const v : A constant map mapping all keys to `v` *)
val const: #key:eqtype -> #value:Type -> value -> Tot (t key value)

(* domain m : The set of keys on which this partial map is defined *)
val domain: #key:eqtype -> #value:Type -> t key value -> Tot (S.set key)

(* contains m k: Decides if key `k` is in the map `m` *)
val contains: #key:eqtype -> #value:Type -> t key value -> key -> Tot bool

(* concat m1 m2 :
      A map whose domain is the union of the domains of `m1` and `m2`.

      Maps every key `k` in the domain of `m1` to `sel m1 k`
      and all other keys to `sel m2 k`.
*)
val concat: #key:eqtype -> #value:Type -> t key value -> t key value -> Tot (t key value)

(* map_val f m:
      A map whose domain is the same as `m` but all values have
      `f` applied to them.
*)
val map_val: #val1:Type -> #val2:Type -> f:(val1 -> val2) -> #key:eqtype -> t key val1 -> Tot (t key val2)

(* restrict s m:
      Restricts the domain of `m` to (domain m `intersect` s)
*)
val restrict: #key:eqtype -> #value:Type -> S.set key -> t key value -> Tot (t key value)

(* const_on dom v: A defined notion, for convenience
     A partial constant map on dom
*)
let const_on (#key:eqtype) (#value:Type) (dom:S.set key) (v:value)
  : t key value
  = restrict dom (const v)


(* map_literal f: A map that is extensionally equal to the function [f] *)
val map_literal (#k:eqtype) (#v:Type) (f: k -> Tot v)
  : t k v

(* disjoint_dom m1 m2:
      Disjoint domains. TODO: its pattern is biased towards `m1`. Why?
 *)
let disjoint_dom (#key:eqtype) (#value:Type) (m1:t key value) (m2:t key value)
  = forall x.{:pattern (contains m1 x)(* ; (contains m2 x) *)} contains m1 x ==> not (contains m2 x)

(* has_dom m dom: A relational version of the `domain m` function *)
let has_dom (#key:eqtype) (#value:Type) (m:t key value) (dom:S.set key)
  = forall x. contains m x <==> S.mem x dom

(* Properties about map functions *)
val lemma_SelUpd1: #key:eqtype -> #value:Type -> m:t key value -> k:key -> v:value ->
                   Lemma (requires True) (ensures (sel (upd m k v) k == v))
                   [SMTPat (sel (upd m k v) k)]

val lemma_SelUpd2: #key:eqtype -> #value:Type -> m:t key value -> k1:key -> k2:key -> v:value ->
                   Lemma (requires True) (ensures (k2=!=k1 ==> sel (upd m k2 v) k1 == sel m k1))
                   [SMTPat (sel (upd m k2 v) k1)]

val lemma_SelConst: #key:eqtype -> #value:Type -> v:value -> k:key ->
                    Lemma (requires True) (ensures (sel (const v) k == v))
                    [SMTPat (sel (const v) k)]

val lemma_SelRestrict: #key:eqtype -> #value:Type -> m:t key value -> ks:S.set key -> k:key ->
                       Lemma (requires True) (ensures (sel (restrict ks m) k == sel m k))
                       [SMTPat (sel (restrict ks m) k)]

val lemma_SelConcat1: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value -> k:key ->
                      Lemma (requires True) (ensures (contains m2 k ==> sel (concat m1 m2) k==sel m2 k))
                      [SMTPat (sel (concat m1 m2) k)]

val lemma_SelConcat2: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value -> k:key ->
                      Lemma (requires True) (ensures (not(contains m2 k) ==> sel (concat m1 m2) k==sel m1 k))
                      [SMTPat (sel (concat m1 m2) k)]

val lemma_SelMapVal: #val1:Type -> #val2:Type -> f:(val1 -> val2) -> #key:eqtype -> m:t key val1 -> k:key ->
                     Lemma (requires True) (ensures (sel (map_val f m) k == f (sel m k)))
                     [SMTPat (sel (map_val f m) k)]

val lemma_InDomUpd1: #key:eqtype -> #value:Type -> m:t key value -> k1:key -> k2:key -> v:value ->
                     Lemma (requires True) (ensures (contains (upd m k1 v) k2 == (k1=k2 || contains m k2)))
                     [SMTPat (contains (upd m k1 v) k2)]

val lemma_InDomUpd2: #key:eqtype -> #value:Type -> m:t key value -> k1:key -> k2:key -> v:value ->
                     Lemma (requires True) (ensures (k2=!=k1 ==> contains (upd m k2 v) k1 == contains m k1))
                     [SMTPat (contains (upd m k2 v) k1)]

val lemma_InDomConstMap: #key:eqtype -> #value:Type -> v:value -> k:key ->
                         Lemma (requires True) (ensures (contains (const v) k))
                         [SMTPat (contains (const v) k)]

val lemma_InDomConcat: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value -> k:key ->
                 Lemma (requires True) (ensures (contains (concat m1 m2) k==(contains m1 k || contains m2 k)))
                 [SMTPat (contains (concat m1 m2) k)]

val lemma_InMapVal: #val1:Type -> #val2:Type -> f:(val1 -> val2) -> #key:eqtype -> m:t key val1 -> k:key ->
                    Lemma (requires True) (ensures (contains (map_val f m) k == contains m k))
                    [SMTPat (contains (map_val f m) k)]

val lemma_InDomRestrict: #key:eqtype -> #value:Type -> m:t key value -> ks:S.set key -> k:key ->
                         Lemma (requires True) (ensures (contains (restrict ks m) k == (S.mem k ks && contains m k)))
                         [SMTPat (contains (restrict ks m) k)]

val lemma_ContainsDom: #key:eqtype -> #value:Type -> m:t key value -> k:key ->
  Lemma (requires True) (ensures (contains m k = S.mem k (domain m)))
                      [SMTPatOr[[SMTPat (contains m k)]; [SMTPat (S.mem k (domain m))]]]

val lemma_UpdDomain : #key:eqtype -> #value:Type -> m:t key value -> k:key -> v:value ->
  Lemma (requires True)
        (ensures (S.equal (domain (upd m k v)) (S.union (domain m) (S.singleton k))))
        [SMTPat (domain (upd m k v))]

val lemma_map_literal (#k:eqtype) (#v:Type) (f: k -> Tot v)
  : Lemma ((forall k.{:pattern (sel (map_literal f) k)} sel (map_literal f) k == f k) /\
           domain (map_literal f) == Set.complement Set.empty)
          [SMTPat (map_literal f)]

(*** Extensional equality ***)

(* equal m1 m2:
      Maps `m1` and `m2` have the same domain and
      and are pointwise equal on that domain.
 *)
val equal (#key:eqtype) (#value:Type) (m1:t key value) (m2:t key value) : prop

(* lemma_equal_intro:
     Introducing `equal m1 m2` by showing maps to be pointwise equal on the same domain
*)
val lemma_equal_intro: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value ->
                       Lemma (requires (forall k. sel m1 k == sel m2 k /\
                                             contains m1 k = contains m2 k))
                             (ensures (equal m1 m2))
                             [SMTPat (equal m1 m2)]

(* lemma_equal_elim:
     Eliminating `equal m1 m2` to provable equality of maps
     Internally, this involves a use of functional extensionality
*)
val lemma_equal_elim: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value ->
                      Lemma (ensures (equal m1 m2 <==> m1 == m2))
                            [SMTPat (equal m1 m2)]

[@@(deprecated "Use lemma_equal_elim instead")]
val lemma_equal_refl: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value ->
                      Lemma  (requires (m1 == m2))
                             (ensures  (equal m1 m2))

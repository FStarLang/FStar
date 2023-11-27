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
module TransparentMap
open FStar.FunctionalExtensionality

module F = FStar.FunctionalExtensionality

type map (k:eqtype) (v:Type) = F.restricted_t k (fun _ -> v)

let sel (#k:eqtype) (#v:Type) (m:map k v) (key:k) : v = m key

let upd (#k:eqtype) (#v:Type) (m:map k v) (key:k) (value:v) : map k v =
  F.on_dom k (fun x -> if x = key then value else sel m x)

let sel_upd1 (#k:eqtype) (#v:Type) (m:map k v) (key:k) (value:v)
  : Lemma
    (ensures (sel (upd m key value) key == value))
    [SMTPat (sel (upd m key value) key)]
  = ()

let sel_upd2 (#k:eqtype) (#v:Type) (m:map k v) (key1:k) (key2:k) (value:v)
  : Lemma
    (ensures (~(key1 == key2) ==> sel (upd m key1 value) key2 == sel m key2))
    [SMTPat (sel (upd m key1 value) key2)]
  = ()

abstract type equal (#key:eqtype) (#value:Type) (m1: map key value) (m2: map key value) =
  feq m1 m2

abstract val lemma_equal_intro: #key:eqtype -> #value:Type -> m1:map key value -> m2:map key value ->
                       Lemma (requires (forall k. sel m1 k == sel m2 k))
                       (ensures (equal m1 m2))
                       [SMTPat (equal m1 m2)]



abstract val lemma_equal_elim: #key:eqtype -> #value:Type -> m1:map key value -> m2:map key value ->
                      Lemma (requires (equal m1 m2)) (ensures  (m1 == m2))
                      [SMTPat (equal m1 m2)]



abstract val lemma_equal_refl: #key:eqtype -> #value:Type -> m1:map key value -> m2:map key value ->
                      Lemma  (requires (m1 == m2)) (ensures  (equal m1 m2))
		      [SMTPat (equal m1 m2)]

let lemma_equal_intro #key #value m1 m2 = ()
let lemma_equal_elim #key #value m1 m2  = ()
let lemma_equal_refl #key #value m1 m2  = ()

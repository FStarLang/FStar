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

module FStar.DependentMap

module F = FStar.FunctionalExtensionality
noeq
type t (key: eqtype) (value: (key -> Type)) = { mappings:F.restricted_t key value }

let create (#key: eqtype) (#value: (key -> Tot Type)) (f: (k: key -> Tot (value k)))
    : Tot (t key value) = { mappings = F.on_domain key f }

let sel (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k: key) : Tot (value k) =
  m.mappings k

let sel_create (#key: eqtype) (#value: (key -> Tot Type)) (f: (k: key -> Tot (value k))) (k: key)
    : Lemma (requires True)
      (ensures (sel #key #value (create f) k == f k))
      [SMTPat (sel #key #value (create f) k)] = ()

let upd (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k: key) (v: value k)
    : Tot (t key value) =
  { mappings = F.on_domain key (fun k' -> if k' = k then v else m.mappings k') }

let sel_upd_same (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k: key) (v: value k) =
  ()

let sel_upd_other
      (#key: eqtype)
      (#value: (key -> Tot Type))
      (m: t key value)
      (k: key)
      (v: value k)
      (k': key)
     = ()

let equal (#key: eqtype) (#value: (key -> Tot Type)) (m1 m2: t key value) =
  forall k. sel m1 k == sel m2 k

let equal_intro (#key: eqtype) (#value: (key -> Tot Type)) (m1 m2: t key value) = ()

let equal_refl (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) = ()

let equal_elim (#key: eqtype) (#value: (key -> Tot Type)) (m1 m2: t key value) =
  F.extensionality key value m1.mappings m2.mappings

let restrict (#key: eqtype) (#value: (key -> Tot Type)) (p: (key -> Tot Type0)) (m: t key value) =
  { mappings = F.on_domain (k: key{p k}) m.mappings }

let sel_restrict
      (#key: eqtype)
      (#value: (key -> Tot Type))
      (p: (key -> Tot Type0))
      (m: t key value)
      (k: key{p k})
     = ()

let concat_mappings
      (#key1: eqtype)
      (#value1: (key1 -> Tot Type))
      (#key2: eqtype)
      (#value2: (key2 -> Tot Type))
      (m1: (k1: key1 -> Tot (value1 k1)))
      (m2: (k2: key2 -> Tot (value2 k2)))
      (k: either key1 key2)
    : concat_value value1 value2 k =
  match k with
  | Inl k1 -> m1 k1
  | Inr k2 -> m2 k2

let concat
      (#key1: eqtype)
      (#value1: (key1 -> Tot Type))
      (#key2: eqtype)
      (#value2: (key2 -> Tot Type))
      (m1: t key1 value1)
      (m2: t key2 value2)
    : Tot (t (either key1 key2) (concat_value value1 value2)) =
  { mappings = F.on_domain (either key1 key2) (concat_mappings m1.mappings m2.mappings) }

let sel_concat_l
      (#key1: eqtype)
      (#value1: (key1 -> Tot Type))
      (#key2: eqtype)
      (#value2: (key2 -> Tot Type))
      (m1: t key1 value1)
      (m2: t key2 value2)
      (k1: key1)
     = ()

let sel_concat_r
      (#key1: eqtype)
      (#value1: (key1 -> Tot Type))
      (#key2: eqtype)
      (#value2: (key2 -> Tot Type))
      (m1: t key1 value1)
      (m2: t key2 value2)
      (k2: key2)
     = ()

let rename
      (#key1: eqtype)
      (#value1: (key1 -> Tot Type))
      (m: t key1 value1)
      (#key2: eqtype)
      (ren: (key2 -> Tot key1))
    : Tot (t key2 (rename_value value1 ren)) =
  { mappings = F.on_domain key2 (fun k2 -> m.mappings (ren k2)) }

let sel_rename
      (#key1: eqtype)
      (#value1: (key1 -> Tot Type))
      (m: t key1 value1)
      (#key2: eqtype)
      (ren: (key2 -> Tot key1))
      (k2: key2)
    : Lemma (ensures (sel (rename m ren) k2 == sel m (ren k2))) = ()

let map
      (#key: eqtype)
      (#value1 #value2: (key -> Tot Type))
      (f: (k: key -> value1 k -> Tot (value2 k)))
      (m: t key value1)
    : Tot (t key value2) = { mappings = F.on_domain key (fun k -> f k (sel m k)) }

let sel_map
      (#key: eqtype)
      (#value1 #value2: (key -> Tot Type))
      (f: (k: key -> value1 k -> Tot (value2 k)))
      (m: t key value1)
      (k: key)
     = ()

let map_upd
      (#key: eqtype)
      (#value1 #value2: (key -> Tot Type))
      (f: (k: key -> value1 k -> Tot (value2 k)))
      (m: t key value1)
      (k: key)
      (v: value1 k)
     = equal_elim #key #value2 (map f (upd m k v)) (upd (map f m) k (f k v))


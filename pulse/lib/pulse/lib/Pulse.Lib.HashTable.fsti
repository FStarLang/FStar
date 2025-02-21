(*
   Copyright 2024 Microsoft Research

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

module Pulse.Lib.HashTable

open Pulse.Lib.Pervasives
open Pulse.Lib.HashTable.Spec
open Pulse.Lib.HashTable.Type

module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module PHT = Pulse.Lib.HashTable.Spec

let lift_hash_fun (#k:eqtype) (hashf:k -> SZ.t) : GTot (k -> nat) =
  fun k -> SZ.v (hashf k)

let mk_init_pht (#k:eqtype) #v (hashf:k -> SZ.t) (sz:pos_us)
: GTot (pht_t k v) = {  
  spec = (fun k -> None);
  repr = {
    sz = SZ.v sz;
    seq = Seq.create (SZ.v sz) Clean;
    hashf = lift_hash_fun hashf;
  };
  inv = ();
}

noextract
let related #kt #vt (ht:ht_t kt vt) (pht:pht_t kt vt) : prop =
  SZ.v ht.sz == pht.repr.sz /\
  pht.repr.hashf == lift_hash_fun ht.hashf

let models #kt #vt (ht:ht_t kt vt) (pht:pht_t kt vt) : slprop =
  V.pts_to ht.contents pht.repr.seq **
  pure (related ht pht /\
        V.is_full_vec ht.contents /\
        SZ.fits (2 `op_Multiply` SZ.v ht.sz))

val models_timeless #kt #vt (ht:ht_t kt vt) (pht:pht_t kt vt)
: Lemma (timeless (models ht pht))
        [SMTPat (timeless (models ht pht))]

let pht_sz #k #v (pht:pht_t k v) : GTot pos = pht.repr.sz

(* A hash table can be created as long as the size isn't too big.
*Twice* the size must fit in a size_t, since this means
overflow will not occur internally when traversing the table.
We could probably relax this to just a fitting in a size_t. *)
val alloc
  (#[@@@ Rust_generics_bounds ["Copy"; "PartialEq"; "Clone"]] k:eqtype)
  (#[@@@ Rust_generics_bounds ["Clone"]] v:Type0)
  (hashf:(k -> SZ.t)) (l:pos_us)
: stt (ht_t k v)
    (requires pure (SZ.fits (2 `op_Multiply` SZ.v l)))
    (ensures fun ht -> exists* pht. models ht pht ** pure (pht == mk_init_pht hashf l))

val dealloc
  (#[@@@ Rust_generics_bounds ["Copy"; "PartialEq"; "Clone"]] k:eqtype)
  (#[@@@ Rust_generics_bounds ["Clone"]] v:Type0)
  (ht:ht_t k v)
: stt unit 
    (requires exists* pht. models ht pht)
    (ensures fun _ -> emp)

noextract
let same_sz_and_hashf (#kt:eqtype) (#vt:Type) (ht1 ht2:ht_t kt vt) : prop =
  ht1.sz == ht2.sz /\
  ht1.hashf == ht2.hashf

val lookup
  (#[@@@ Rust_generics_bounds ["Copy"; "PartialEq"; "Clone"]] kt:eqtype)
  (#[@@@ Rust_generics_bounds ["Clone"]] vt:Type0)
  (#pht:erased (pht_t kt vt))
  (ht:ht_t kt vt)
  (k:kt)
: stt (ht_t kt vt & option SZ.t)
    (requires models ht pht)
    (ensures fun p ->
       models (fst p) pht ** 
       pure (same_sz_and_hashf (fst p) ht /\ (snd p == PHT.lookup_index_us pht k)))

val replace
  (#[@@@ Rust_generics_bounds ["Copy"; "PartialEq"; "Clone"]] kt:eqtype)
  (#[@@@ Rust_generics_bounds ["Clone"]] vt:Type0)
  (#pht:erased (pht_t kt vt))
  (ht:ht_t kt vt)
  (idx:SZ.t)
  (k:kt)
  (v:vt)
  (_:squash (SZ.v idx < Seq.length pht.repr.seq /\ PHT.lookup_index_us pht k == Some idx))
: stt (ht_t kt vt & vt)  
    (requires models ht pht)
    (ensures fun p ->
       models (fst p) (PHT.upd_pht #kt #vt pht idx k v ()) **
       pure (same_sz_and_hashf (fst p) ht /\ Some (snd p) == PHT.lookup pht k))

val insert
  (#[@@@ Rust_generics_bounds ["Copy"; "PartialEq"; "Clone"]] kt:eqtype)
  (#[@@@ Rust_generics_bounds ["Clone"]] vt:Type0)
  (ht:ht_t kt vt) (k:kt) (v:vt)
  (#pht:(p:erased (pht_t kt vt){PHT.not_full p.repr}))
: stt (ht_t kt vt & bool)
    (requires models ht pht)
    (ensures fun b ->
       exists* pht'.
         models (fst b) pht' **
         pure (same_sz_and_hashf (fst b) ht /\
               (if snd b then pht' == PHT.insert pht k v
                else pht' == reveal pht)))

val not_full
  (#[@@@ Rust_generics_bounds ["Copy"; "PartialEq"; "Clone"]] kt:eqtype)
  (#[@@@ Rust_generics_bounds ["Clone"]] vt:Type0)
  (ht:ht_t kt vt)
  (#pht:erased (pht_t kt vt))
: stt (ht_t kt vt & bool)
    (requires models ht pht)
    (ensures fun b ->
       models (fst b) pht ** 
       pure (same_sz_and_hashf (fst b) ht /\ (snd b ==> PHT.not_full pht.repr)))

val insert_if_not_full
  (#[@@@ Rust_generics_bounds ["Copy"; "PartialEq"; "Clone"]] kt:eqtype)
  (#[@@@ Rust_generics_bounds ["Clone"]] vt:Type0)
  (ht:ht_t kt vt) (k:kt) (v:vt)
  (#pht:erased (PHT.pht_t kt vt))
: stt (ht_t kt vt & bool)
    (requires models ht pht)
    (ensures fun b ->
       exists* pht'.
         models (fst b) pht' **
         pure (same_sz_and_hashf (fst b) ht /\
               (if snd b
                then (PHT.not_full (reveal pht).repr /\
                      pht'==PHT.insert pht k v)
                else pht' == reveal pht)))

val delete
  (#[@@@ Rust_generics_bounds ["Copy"; "PartialEq"; "Clone"]] kt:eqtype)
  (#[@@@ Rust_generics_bounds ["Clone"]] vt:Type0)
  (ht:ht_t kt vt) (k:kt)
  (#pht:erased (pht_t kt vt))
: stt (ht_t kt vt & bool)
    (requires models ht pht)
    (fun b ->
       (exists* pht'. 
          models (fst b) pht' **
          pure (same_sz_and_hashf (fst b) ht /\
                (if snd b then pht' == PHT.delete pht k else pht' == reveal pht))))

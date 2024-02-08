(*
   Copyright 2023 Microsoft Research

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

module Pulse.Lib.HashTable.Type

open Pulse.Lib.Pervasives
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT

open Pulse.Lib.HashTable.Spec

type pos_us = n:SZ.t{SZ.v n > 0}

[@@ no_auto_projectors;
    Rust_generics_bounds [["Copy"; "PartialEq"; "Clone"];
                          ["Clone"]] ]
noeq
type ht_t (keyt:eqtype) (valt:Type) = {
  sz : pos_us;
  hashf: keyt -> SZ.t;
  contents : V.vec (cell keyt valt);
}

val token (#k:eqtype) (#v:Type0)
  (r:ref (ht_t k v))
  (r_sz:ref pos_us)
  (r_hashf:ref (k -> SZ.t))
  (r_contents:ref (V.vec (cell k v))) : vprop

let exploded_vp (#k:eqtype) (#v:Type0)
  (r:ref (ht_t k v))
  (ht:ht_t k v)
  (r_sz:ref pos_us)
  (r_hashf:ref (k -> SZ.t))
  (r_contents:ref (V.vec (cell k v))) : vprop =  
  pts_to r_sz ht.sz **
  pts_to r_hashf ht.hashf **
  pts_to r_contents ht.contents **
  token r r_sz r_hashf r_contents

val explode_ref_ht_t (#k:eqtype) (#v:Type0) (#ht:erased (ht_t k v)) (r:ref (ht_t k v))
  : stt (ref pos_us & ref (k -> SZ.t) & ref (V.vec (cell k v)))
        (requires pts_to r ht)
        (ensures fun res -> exploded_vp r ht (tfst res) (tsnd res) (tthd res))

val unexplode_ref (#k:eqtype) (#v:Type0) (#ht:erased (ht_t k v))
  (r:ref (ht_t k v))
  (r_sz:ref pos_us)
  (r_hashf:ref (k -> SZ.t))
  (r_contents:ref (V.vec (cell k v)))
  : stt unit
        (requires exploded_vp r ht r_sz r_hashf r_contents)
        (ensures fun _ -> pts_to r ht)

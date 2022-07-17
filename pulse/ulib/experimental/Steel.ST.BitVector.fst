(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Aseem Rastogi
*)

module Steel.ST.BitVector

open Steel.ST.Effect.Ghost
open Steel.ST.Effect
open Steel.ST.Util

module U32 = FStar.UInt32
module G = FStar.Ghost
module A = Steel.ST.Array

/// Implementation of bv_t using an array of bool

type bv_t n = a:A.array bool{A.length a == U32.v n /\ A.is_full_array a}

let pts_to bv p s = A.pts_to bv p s

let pts_to_length bv s = A.pts_to_length bv s

let alloc n = A.alloc false n

let bv_is_set bv i = A.read bv i

let bv_set #_ #s bv i = A.write #_ bv #s i true

let bv_unset #_ #s bv i = A.write #_ bv #s i false

let free #n #s bv =
  intro_exists (G.reveal s) (A.pts_to bv full_perm);
  A.free bv

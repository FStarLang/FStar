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

module U32 = FStar.UInt32
module G = FStar.Ghost

val bv_t (n:U32.t) : Type0

type repr = Seq.seq bool

val pts_to (#n:U32.t) (bv:bv_t n) (s:repr) : vprop

val pts_to_length (#opened:_) (#n:U32.t) (bv:bv_t n) (s:repr)
  : STGhost unit opened
      (pts_to bv s)
      (fun _ -> pts_to bv s)
      (requires True)
      (ensures fun _ -> Seq.length s == U32.v n)

val alloc (n:U32.t{U32.v n > 0})
  : STT (bv_t n) emp (fun r -> pts_to r (Seq.create (U32.v n) false))

val bv_is_set
  (#n:U32.t)
  (#s:G.erased repr)
  (bv:bv_t n)
  (i:U32.t{U32.v i < Seq.length s})
  : ST bool
       (pts_to bv s)
       (fun _ -> pts_to bv s)
       (requires True)
       (ensures fun b -> b == Seq.index s (U32.v i))

val bv_set
  (#n:U32.t)
  (#s:G.erased repr)
  (bv:bv_t n)
  (i:U32.t{U32.v i < Seq.length s})
  : STT unit
       (pts_to bv s)
       (fun _ -> pts_to bv (Seq.upd s (U32.v i) true))

val bv_unset
  (#n:U32.t)
  (#s:G.erased repr)
  (bv:bv_t n)
  (i:U32.t{U32.v i < Seq.length s})
  : STT unit
       (pts_to bv s)
       (fun _ -> pts_to bv (Seq.upd s (U32.v i) false))

val free
  (#n:U32.t)
  (#s:G.erased repr)
  (bv:bv_t n)
  : STT unit (pts_to bv s) (fun _ -> emp)

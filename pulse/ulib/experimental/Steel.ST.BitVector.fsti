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

/// A bitvector implementation with fractional permission based ownership
///
/// It presents logical view of the bitvector as a sequence of booleans

module Steel.ST.BitVector

open Steel.ST.Effect.Ghost
open Steel.ST.Effect
open Steel.FractionalPermission

module U32 = FStar.UInt32
module G = FStar.Ghost

/// The bitvector of size n

val bv_t (n:U32.t) : Type0

/// Logical representation as a sequence of bool

type repr = Seq.seq bool

/// The pts_to assertion, bv pts_to p s

val pts_to (#n:U32.t) (bv:bv_t n) (p:perm) (s:repr) : vprop

/// A stateful lemma that related the length of the vector to the length of its repr

val pts_to_length (#opened:_) (#n:U32.t) (#p:perm) (bv:bv_t n) (s:repr)
  : STGhost unit opened
      (pts_to bv p s)
      (fun _ -> pts_to bv p s)
      (requires True)
      (ensures fun _ -> Seq.length s == U32.v n)

/// `alloc`, initially all the bits are unset

val alloc (n:U32.t{U32.v n > 0})
  : STT (bv_t n) emp (fun r -> pts_to r full_perm (Seq.create (U32.v n) false))

/// Returns whether ith bit in the bitvector is set

val bv_is_set
  (#n:U32.t)
  (#p:perm)
  (#s:G.erased repr)
  (bv:bv_t n)
  (i:U32.t{U32.v i < Seq.length s})
  : ST bool
       (pts_to bv p s)
       (fun _ -> pts_to bv p s)
       (requires True)
       (ensures fun b -> b == Seq.index s (U32.v i))

/// Sets the its bit in the bitvector

val bv_set
  (#n:U32.t)
  (#s:G.erased repr)
  (bv:bv_t n)
  (i:U32.t{U32.v i < Seq.length s})
  : STT unit
       (pts_to bv full_perm s)
       (fun _ -> pts_to bv full_perm (Seq.upd s (U32.v i) true))

/// Unsets the its bit in the bitvector

val bv_unset
  (#n:U32.t)
  (#s:G.erased repr)
  (bv:bv_t n)
  (i:U32.t{U32.v i < Seq.length s})
  : STT unit
       (pts_to bv full_perm s)
       (fun _ -> pts_to bv full_perm (Seq.upd s (U32.v i) false))

/// `free`

val free
  (#n:U32.t)
  (#s:G.erased repr)
  (bv:bv_t n)
  : STT unit (pts_to bv full_perm s) (fun _ -> emp)

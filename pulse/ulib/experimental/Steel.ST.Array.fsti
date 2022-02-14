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
*)
module Steel.ST.Array
open FStar.Ghost
open Steel.ST.Util
open Steel.FractionalPermission
open FStar.Seq
module U32 = FStar.UInt32

(** This module provides an array type, with fractional permissions based
    ownership over the entire array.

    This is non-selector variant of the Steel.Array library.
    
    A variant of it with splitting ownership over sub-arrays would be nice,
    but doesn't exist yet. *)

/// Abstract datatype for a Steel array of type [t]
val array (t:Type u#0) : Type u#0

/// Returns the length of the array. Usable for specification and proof purposes,
/// as modeled by the GTot effect
val length (#t:_) (r:array t) : GTot nat

/// An abbreviation refining an array by its length

inline_for_extraction
let larray (t:Type) (n:nat) = a:array t{ length a = n }

/// The main representation predicate
///
/// A big design decision in this library was whether the second index
/// of this predicate should be a [lseq t (length a)] or just a [seq t].
///
/// Making it an [lseq] forces every specification to be strongly
/// typed, in the sense that the logical representation of an array
/// has to be a sequence of the right length. This can be a little
/// cumbersome in specifications, particularly as the refinement appears
/// in some cases beneath the [erased] constructor.
///
/// So, we opted instead to let the index be just a [seq t], and
/// requiring length refinements on it in certain functions, only when
/// necessary.
val pts_to (#t:Type)
           (a:array t)
           (p:perm)
           ([@@@smt_fallback] s:seq t)
  : vprop

/// This ghost function proves that an array always points to a
/// sequence of the appropriate length
val pts_to_length (#t:Type) (#o:inames) (#p:perm) (a:array t) (s:seq t)
  : STGhost unit o
      (pts_to a p s)
      (fun _ -> pts_to a p s)
      (requires True)
      (ensures fun _ -> Seq.length s == length a)

/// Allocates an array of length n, where all elements of the array initially are [x]
val alloc (#t:Type)
          (x:t)
          (n:U32.t)
  : STT (larray t (U32.v n))
        emp
        (fun r -> pts_to r full_perm (Seq.create (U32.v n) x))

/// Accesses index [i] in array [r], as long as [i] is in bounds and the array
/// is currently valid in memory
val read (#t:Type) (#p:perm)
         (a:array t)
         (#s:erased (seq t))
         (i:U32.t { U32.v i < Seq.length s })
  : ST t
       (pts_to a p s)
       (fun _ -> pts_to a p s)
       (requires True)
       (ensures fun v -> 
         v == Seq.index s (U32.v i))

/// Updates index [i] in array [r] with value [x], as long as [i]
/// is in bounds and the array is currently valid in memory
val write (#t:Type)
          (a:array t)
          (#s:erased (seq t))
          (i:U32.t { U32.v i < Seq.length s })
          (x:t)
  : STT unit
       (pts_to a full_perm s)
       (fun _ -> pts_to a full_perm (Seq.upd s (U32.v i) x))

/// Frees array [r], as long as it initially was a valid array in memory
val free (#t:Type) (a:array t)
  : STT unit
       (exists_ (pts_to a full_perm))
       (fun _ -> emp)

/// Copies the contents of a0 to a1
val memcpy (#t:_) (#p0:perm)
           (a0 a1:array t)
           (#s0 #s1:erased (seq t))
           (l:U32.t { U32.v l == length a0 /\ length a0 == length a1 } )
  : STT unit
    (pts_to a0 p0 s0 `star` pts_to a1 full_perm s1)
    (fun _ -> pts_to a0 p0 s0  `star` pts_to a1 full_perm s0)

/// Decides whether the contents of a0 and a1 are equal
val compare (#t:eqtype) (#p0 #p1:perm)
            (a0 a1:array t)
            (#s0 #s1:erased (seq t))
            (l:U32.t { U32.v l == length a0 /\ length a0 == length a1 } )
  : ST bool
    (pts_to a0 p0 s0 `star` pts_to a1 p1 s1)
    (fun _ -> pts_to a0 p0 s0 `star` pts_to a1 p1 s1)
    (requires True)
    (ensures fun b -> b <==> eq2 #(Seq.seq t) s0 s1)

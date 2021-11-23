(*
   Copyright 2020 Microsoft Research

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
module U32 = FStar.UInt32

/// Abstract datatype for a Steel array of type [t]
val array (t:Type u#0) : Type u#0

/// Returns the length of the array. Usable for specification and proof purposes,
/// as modeled by the GTot effect
val length (#t:_) (r:array t) : GTot nat

/// The contents of an array of type [t] is a sequence of values of type [t]
let contents (t:Type u#0) (n:nat) = FStar.Seq.lseq t n

let repr (#t:Type) (a:array t) = contents t (length a)

let larray (t:Type) (n:nat) = a:array t{ length a = n }

/// The main representation predicate
val pts_to (#t:Type)
           (a:array t)
           ([@@@smt_fallback] s:repr a)
  : vprop

/// Allocates an array of length n, where all elements of the array initially are [x]
val alloc (#t:Type)
          (x:t)
          (n:U32.t)
  : STT (larray t (U32.v n))
        emp
        (fun r -> pts_to r (Seq.create (U32.v n) x))

/// Accesses index [i] in array [r], as long as [i] is in bounds and the array
/// is currently valid in memory
val read (#t:Type) 
         (a:array t)
         (#s:erased (repr a))
         (i:U32.t { U32.v i < length a })
  : ST t
       (pts_to a s)
       (fun _ -> pts_to a s)
       (requires True)
       (ensures fun v -> 
         v == Seq.index s (U32.v i))

/// Updates index [i] in array [r] with value [x], as long as [i]
/// is in bounds and the array is currently valid in memory
val write (#t:Type)
          (a:array t)
          (#s:erased (repr a))
          (i:U32.t { U32.v i < length a })
          (x:t)
  : STT unit
       (pts_to a s)
       (fun _ -> pts_to a (Seq.upd s (U32.v i) x))

/// Frees array [r], as long as it initially was a valid array in memory
val free (#t:Type) (a:array t)
  : STT unit
       (exists_ (pts_to a))
       (fun _ -> emp)

/// Copies the contents of a0 to a1
val memcpy (#t:_)
           (a0 a1:array t)
           (#s0:erased (repr a0))
           (#s1:erased (repr a1))
           (l:U32.t { U32.v l == length a0 /\ length a0 == length a1 } )
  : STT unit
    (pts_to a0 s0 `star` pts_to a1 s1)
    (fun _ -> pts_to a0 s0  `star` pts_to a1 s0)

/// Decides whether the contents of a0 and a1 are equal
val compare (#t:eqtype)
            (a0 a1:array t)
            (#s0:erased (repr a0))
            (#s1:erased (repr a1))
            (l:U32.t { U32.v l == length a0 /\ length a0 == length a1 } )
  : ST bool
    (pts_to a0 s0 `star` pts_to a1 s1)
    (fun _ -> pts_to a0 s0 `star` pts_to a1 s1)
    (requires True)
    (ensures fun b -> b <==> eq2 #(Seq.seq t) s0 s1)

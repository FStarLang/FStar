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

module Steel.ST.Array.Util

module G = FStar.Ghost
module U32 = FStar.UInt32

module A = Steel.ST.Array

open Steel.FractionalPermission
open Steel.ST.Effect

/// Some utilities for steel arrays


/// Create an array whose elements are specified by the input function

inline_for_extraction
val array_literal
  (#a:Type0)
  (n:U32.t)
  (f:(i:U32.t{U32.v i < U32.v n} -> a))
  : ST (A.array a)
       emp
       (fun arr ->
        A.pts_to arr full_perm (Seq.init (U32.v n) (fun i -> f (U32.uint_to_t i))))
       (requires U32.v n > 0)
       (ensures fun arr -> A.length arr == U32.v n)


/// Check if all the elements of an array satisfy a predicate

inline_for_extraction
val for_all
  (#a:Type0)
  (#perm:perm)
  (#s:G.erased (Seq.seq a))
  (n:U32.t)
  (arr:A.array a)
  (p:a -> bool)
  : ST bool
       (A.pts_to arr perm s)
       (fun _ -> A.pts_to arr perm s)
       (requires A.length arr == U32.v n)
       (ensures fun b -> b <==> (forall (i:nat). i < Seq.length s ==>
                                    p (Seq.index s i)))

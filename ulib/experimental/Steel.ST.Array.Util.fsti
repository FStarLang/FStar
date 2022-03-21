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
open Steel.ST.Util

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


/// for_all2, for predicates over elements of two arrays

inline_for_extraction
val for_all2
  (#a #b:Type0)
  (#p0 #p1:perm)
  (#s0:G.erased (Seq.seq a))
  (#s1:G.erased (Seq.seq b))
  (n:U32.t)
  (a0:A.array a)
  (a1:A.array b)
  (p:a -> b -> bool)
  : ST bool
       (A.pts_to a0 p0 s0
          `star`
        A.pts_to a1 p1 s1)
       (fun _ ->
        A.pts_to a0 p0 s0
          `star`
        A.pts_to a1 p1 s1)
       (requires
         A.length a0 == U32.v n /\
         A.length a0 == A.length a1)
       (ensures fun b -> b <==> (forall (i:nat). (i < Seq.length s0 /\ i < Seq.length s1) ==>
                                    p (Seq.index s0 i) (Seq.index s1 i)))


/// An array compare function that uses for_all2
///   to loop over the two arrays and compre their elements

let compare (#a:eqtype) (#p0 #p1:perm)
  (a0 a1:A.array a)
  (#s0 #s1:G.erased (Seq.seq a))
  (n:U32.t{U32.v n == A.length a0 /\ A.length a0 == A.length a1})
  : ST bool
       (A.pts_to a0 p0 s0
          `star`
        A.pts_to a1 p1 s1)

       (fun _ ->
        A.pts_to a0 p0 s0
          `star`
        A.pts_to a1 p1 s1)
       (requires True)
       (ensures fun b -> b <==> s0 == s1)
  = let b = for_all2 n a0 a1 (fun x y -> x = y) in
    A.pts_to_length a0 s0;
    A.pts_to_length a1 s1;
    assert (b <==> Seq.equal s0 s1);
    return b

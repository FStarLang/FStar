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

(* A partial model for C array pointers. Given a type t, we model type
   t* with the following operations:

   * alloc, free

   * read at some offset p[i]
   
   * additive pointer arithmetic: if p is an array pointer, then the
     user has permission to access n cells to its right-hand-side (no
     subtractions.) So if i <= n, then operation q = p+i splits the
     permission into two parts, p for cells from 0 to i-1, and q for
     cells from i to n-1. User needs to explicitly return the
     permission by "merging" back q into p.
*)

module Steel.ArrayPtr
open Steel.Memory
open Steel.Effect
open Steel.FractionalPermission
open Steel.Effect.Atomic
module U32 = FStar.UInt32
module A = Steel.Array

val t (t:Type u#0) : Type u#0

noeq type v (t: Type u#0) = {
  array: A.array t;                      (* spatial permission range *)
  contents: Seq.lseq t (A.length array); (* actual contents *)
}

val is_arrayptr (#a:Type0) (r:t a) (p: perm) : slprop u#1
val arrayptr_sel (#a:Type0) (r:t a) (p: perm) : selector (v a) (is_arrayptr r p)

[@@ __steel_reduce__]
let varrayptr' #a r p : vprop' =
  {hp = is_arrayptr r p;
   t = v a;
   sel = arrayptr_sel r p}

[@@ __steel_reduce__]
let varrayptrp r p = VUnit (varrayptr' r p)

[@@ __steel_reduce__]
let varrayptr r = varrayptrp r full_perm

[@@ __steel_reduce__]
let sel (#a:Type) (#p:vprop) (r:t a)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (varrayptr r) /\ True)})
: GTot (v a)
  = h (varrayptr r)


(* Splitting an array (inspired from Steel.Array) *)

val joinp (#opened: _) (#a:Type) (al ar:t a) (p: perm)
  : SteelGhost unit opened
          (varrayptrp al p `star` varrayptrp ar p)
          (fun _ -> varrayptrp al p)
          (fun h -> A.adjacent (h (varrayptrp al p)).array (h (varrayptrp ar p)).array)
          (fun h _ h' ->
            let cl = h (varrayptrp al p) in
            let cr = h (varrayptrp ar p) in
            let c' = h' (varrayptrp al p) in
            A.merge_into cl.array cr.array c'.array /\
            c'.contents == cl.contents `Seq.append` cr.contents
          )

let join (#opened: _) (#a:Type) (al ar:t a)
  : SteelGhost unit opened
          (varrayptr al `star` varrayptr ar)
          (fun _ -> varrayptr al)
          (fun h -> A.adjacent (h (varrayptr al)).array (h (varrayptr ar)).array)
          (fun h _ h' ->
            let cl = h (varrayptr al) in
            let cr = h (varrayptr ar) in
            let c' = h' (varrayptr al) in
            A.merge_into cl.array cr.array c'.array /\
            c'.contents == cl.contents `Seq.append` cr.contents
          )
=
  joinp _ _ _

val splitp (#a:Type) (x: t a) (p: perm) (i:U32.t)
  : Steel (t a)
          (varrayptrp x p)
          (fun res -> varrayptrp x p `star` varrayptrp res p)
          (fun h -> U32.v i <= A.length (h (varrayptrp x p)).array)
          (fun h res h' ->
            let s = h (varrayptrp x p) in
            let sl = h' (varrayptrp x p) in
            let sr = h' (varrayptrp res p) in
            U32.v i <= A.length s.array /\
            A.merge_into sl.array sr.array s.array /\
            sl.contents == Seq.slice s.contents 0 (U32.v i) /\
            sr.contents == Seq.slice s.contents (U32.v i) (A.length s.array) /\
            s.contents == sl.contents `Seq.append` sr.contents
          )

let split (#a:Type) (x: t a) (i:U32.t)
  : Steel (t a)
          (varrayptr x)
          (fun res -> varrayptr x `star` varrayptr res)
          (fun h -> U32.v i <= A.length (h (varrayptr x)).array)
          (fun h res h' ->
            let s = h (varrayptr x) in
            let sl = h' (varrayptr x) in
            let sr = h' (varrayptr res) in
            U32.v i <= A.length s.array /\
            A.merge_into sl.array sr.array s.array /\
            sl.contents == Seq.slice s.contents 0 (U32.v i) /\
            sr.contents == Seq.slice s.contents (U32.v i) (A.length s.array) /\
            s.contents == sl.contents `Seq.append` sr.contents
          )
=
  splitp _ _ i

val alloc (#a:Type) (x:a) (n:U32.t)
  : Steel (t a)
             emp
             (fun r -> varrayptr r)
             (requires fun _ -> True)
             (ensures fun _ r h1 ->
               (h1 (varrayptr r)).contents == Seq.create (U32.v n) x /\
               A.freeable (h1 (varrayptr r)).array
             )

val indexp (#a:Type) (r: t a) (p: perm) (i:U32.t)
  : Steel a
             (varrayptrp r p)
             (fun _ -> varrayptrp r p)
             (requires fun h -> U32.v i < A.length (h (varrayptrp r p)).array)
             (ensures fun h0 y h1 ->
               let s = h0 (varrayptrp r p) in
               h1 (varrayptrp r p) == s /\
               U32.v i < A.length s.array /\
               y == Seq.index s.contents (U32.v i))

let index (#a:Type) (r: t a) (i:U32.t)
  : Steel a
             (varrayptr r)
             (fun _ -> varrayptr r)
             (requires fun h -> U32.v i < A.length (h (varrayptr r)).array)
             (ensures fun h0 y h1 ->
               let s = h0 (varrayptr r) in
               h1 (varrayptr r) == s /\
               U32.v i < A.length s.array /\
               y == Seq.index s.contents (U32.v i))
=
  indexp _ _ i

val upd (#a:Type) (r: t a) (i:U32.t) (x:a)
  : Steel unit
             (varrayptr r)
             (fun _ -> varrayptr r)
             (requires fun h -> U32.v i < A.length (h (varrayptr r)).array)
             (ensures fun h0 _ h1 ->
               let s = h0 (varrayptr r) in
               let s' = h1 (varrayptr r) in
               s'.array == s.array /\
               U32.v i < A.length s.array /\
               s'.contents == Seq.upd s.contents (U32.v i) x)

val free (#a:Type) (r:t a)
  : Steel unit
             (varrayptr r)
             (fun _ -> emp)
             (requires fun h -> A.freeable (h (varrayptr r)).array)
             (ensures fun _ _ _ -> True)

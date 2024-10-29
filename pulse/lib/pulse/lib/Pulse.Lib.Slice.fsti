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

module Pulse.Lib.Slice
open FStar.Tactics.V2
open Pulse.Lib.Pervasives
module SZ = FStar.SizeT
module A = Pulse.Lib.Array

val slice : Type0 -> Type0

val len (#t: Type) : slice t -> SZ.t

instance val has_pts_to_slice (t: Type u#0) : has_pts_to (slice t) (Seq.seq t)

val pts_to_is_slprop2 (#a:Type) (x:slice a) (p:perm) (s:Seq.seq a)
  : Lemma (is_slprop2 (pts_to x #p s))
          [SMTPat (is_slprop2 (pts_to x #p s))]

val pts_to_len (#t: Type) (s: slice t) (#p: perm) (#v: Seq.seq t) : stt_ghost unit emp_inames
    (pts_to s #p v)
    (fun _ -> pts_to s #p v ** pure (Seq.length v == SZ.v (len s)))

val is_from_array (#t: Type) (a: array t) (s: slice t) : slprop

val from_array (#t: Type) (a: array t) (#p: perm) (alen: SZ.t) (#v: Ghost.erased (Seq.seq t) { SZ.v alen == A.length a }) : stt (slice t)
    (A.pts_to a #p v)
    (fun s -> pts_to s #p v ** is_from_array a s)

val to_array (#t: Type) (s: slice t) (#p: perm) (#v: Seq.seq t) (#a: array t) : stt_ghost unit emp_inames
    (pts_to s #p v ** is_from_array a s)
    (fun _ -> A.pts_to a #p v)

(* Written x.(i) *)
val op_Array_Access
        (#t: Type)
        (a: slice t)
        (i: SZ.t)
        (#p: perm)
        (#s: Ghost.erased (Seq.seq t){SZ.v i < Seq.length s})
  : stt t
        (requires
            pts_to a #p s)
        (ensures fun res ->
            pts_to a #p s **
            pure (res == Seq.index s (SZ.v i)))


(* Written a.(i) <- v *)
val op_Array_Assignment
        (#t: Type)
        (a: slice t)
        (i: SZ.t)
        (v: t)
        (#s: Ghost.erased (Seq.seq t) {SZ.v i < Seq.length s})
  : stt unit
        (requires
            pts_to a s)
        (ensures fun res ->
            pts_to a (Seq.upd s (SZ.v i) v))

val share
  (#a:Type)
  (arr:slice a)
  (#s:Ghost.erased (Seq.seq a))
  (#p:perm)
: stt_ghost unit emp_inames
      (requires pts_to arr #p s)
      (ensures fun _ -> pts_to arr #(p /. 2.0R) s ** pts_to arr #(p /. 2.0R) s)

[@@allow_ambiguous]
val gather
  (#a:Type)
  (arr:slice a)
  (#s0 #s1:Ghost.erased (Seq.seq a))
  (#p0 #p1:perm)
: stt_ghost unit emp_inames
      (requires pts_to arr #p0 s0 ** pts_to arr #p1 s1)
      (ensures fun _ -> pts_to arr #(p0 +. p1) s0 ** pure (s0 == s1))

val is_split (#t: Type) (s: slice t) (left: slice t) (right: slice t) : slprop

val is_split_is_slprop2 (#t: Type) (s: slice t) (left: slice t) (right: slice t)
  : Lemma (is_slprop2 (is_split s left right))
          [SMTPat (is_slprop2 (is_split s left right))]

val split (#t: Type) (s: slice t) (#p: perm) (i: SZ.t) (#v: Ghost.erased (Seq.seq t) { SZ.v i <= Seq.length v }) : stt (slice t & slice t)
    (requires pts_to s #p v)
    (ensures fun (s1, s2) ->
      pts_to s1 #p (Seq.slice v 0 (SZ.v i)) **
      pts_to s2 #p (Seq.slice v (SZ.v i) (Seq.length v)) **
      is_split s s1 s2)

val join (#t: Type) (s1: slice t) (#p: perm) (#v1: Seq.seq t) (s2: slice t) (#v2: Seq.seq t) (s: slice t) : stt_ghost unit emp_inames
    (pts_to s1 #p v1 ** pts_to s2 #p v2 ** is_split s s1 s2)
    (fun _ -> pts_to s #p (Seq.append v1 v2))

(* `subslice_rest r s p i j v` is the resource remaining after taking the subslice `r = s[i..j]` *)
let subslice_rest #t (r: slice t) (s: slice t) p (i j: SZ.t) (v: erased (Seq.seq t) { SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length v }) : slprop =
  exists* s1 s2 s3.
    is_split s s1 s2 **
    is_split s2 r s3 **
    pts_to s1 #p (Seq.slice v 0 (SZ.v i)) **
    pts_to s3 #p (Seq.slice v (SZ.v j) (Seq.length v))

val subslice #t (s: slice t) #p (i j: SZ.t) (#v: erased (Seq.seq t) { SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length v }) :
  stt (slice t) (pts_to s #p v)
    fun res -> pts_to res #p (Seq.slice v (SZ.v i) (SZ.v j)) ** subslice_rest res s p i j v

val copy (#t: Type) (dst: slice t) (#p: perm) (src: slice t) (#v: Ghost.erased (Seq.seq t)) : stt unit
    (exists* v_dst . pts_to dst v_dst ** pts_to src #p v ** pure (len src == len dst))
    (fun _ -> pts_to dst v ** pts_to src #p v)

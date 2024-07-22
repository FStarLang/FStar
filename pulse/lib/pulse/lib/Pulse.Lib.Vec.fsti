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

module Pulse.Lib.Vec
#lang-pulse
open FStar.Ghost
open PulseCore.FractionalPermission
open Pulse.Lib.Core

module SZ = FStar.SizeT
module Seq = FStar.Seq
module T = FStar.Tactics.V2

module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array.Core

val vec ([@@@strictly_positive] a:Type0) : Type u#0

val length (#a:Type0) (v:vec a) : GTot nat

inline_for_extraction
type lvec (a:Type0) (n:nat) = v:vec a { length v == n }

val is_full_vec (#a:Type0) (v:vec a) : prop

val pts_to
  (#a:Type0)
  ([@@@equate_strict] v:vec a)
  (#[T.exact (`1.0R)] p:perm)
  (s:Seq.seq a)
: slprop

val pts_to_is_slprop2 (#a:Type0) (v:vec a) (p:perm) (s:Seq.seq a)
  : Lemma (is_slprop2 (pts_to v #p s))
          [SMTPat (is_slprop2 (pts_to v #p s))]

val pts_to_len (#a:Type0) (v:vec a) (#p:perm) (#s:Seq.seq a)
  : stt_ghost unit emp_inames
      (pts_to v #p s)
      (fun _ → pts_to v #p s ** pure (length v == Seq.length s))

val alloc 
  (#a:Type0)
  (x:a)
  (n:SZ.t)
  : stt (vec a)
        (requires emp)
        (ensures fun v ->
           pts_to v (Seq.create (SZ.v n) x) **
           pure (length v == SZ.v n /\ is_full_vec v))

(* Written x.(i) *)
val op_Array_Access
  (#a: Type0)
  (v:vec a)
  (i:SZ.t)
  (#p:perm)
  (#s:Ghost.erased (Seq.seq a) { SZ.v i < Seq.length s })
  : stt a
        (requires pts_to v #p s)
        (ensures fun res ->
           pts_to v #p s **
           pure (res == Seq.index s (SZ.v i)))


(* Written x.(i) <- v *)
val op_Array_Assignment
  (#a:Type0)
  (v:vec a)
  (i:SZ.t)
  (x:a)
  (#s:Ghost.erased (Seq.seq a) { SZ.v i < Seq.length s })
  : stt unit
        (requires pts_to v s)
        (ensures fun _ -> pts_to v (Seq.upd s (SZ.v i) x))

val free
  (#a:Type0)
  (v:vec a)
  (#s:Ghost.erased (Seq.seq a))
  : stt unit
        (requires
           pts_to v s **
           pure (is_full_vec v))
        (ensures fun _ -> emp)

val share
  (#a:Type)
  (v:vec a)
  (#s:Ghost.erased (Seq.seq a))
  (#p:perm)
  : stt_ghost unit emp_inames
      (requires pts_to v #p s)
      (ensures fun _ -> pts_to v #(p /. 2.0R) s ** pts_to v #(p /. 2.0R) s)

[@@allow_ambiguous]
val gather
  (#a:Type)
  (v:vec a)
  (#s0 #s1:Ghost.erased (Seq.seq a))
  (#p0 #p1:perm)
  : stt_ghost unit emp_inames
      (requires pts_to v #p0 s0 ** pts_to v #p1 s1)
      (ensures fun _ -> pts_to v #(p0 +. p1) s0 ** pure (s0 == s1))

val vec_to_array (#a:Type0) (v:vec a) : arr:A.array a { A.length arr == length v }

ghost
fn to_array_pts_to (#a:Type0) (v:vec a) (#p:perm) (#s:Seq.seq a)
requires pts_to v #p s
ensures A.pts_to (vec_to_array v) #p s

ghost
fn to_vec_pts_to (#a:Type0) (v:vec a) (#p:perm) (#s:Seq.seq a)
requires A.pts_to (vec_to_array v) #p s
ensures pts_to v #p s

val read_ref (#a:Type0) (r:R.ref (vec a))
  (i:SZ.t)
  (#v:erased (vec a))
  (#s:erased (Seq.seq a) { SZ.v i < Seq.length s})
  : stt a
    (requires R.pts_to r v ** pts_to v s)
    (ensures fun res -> R.pts_to r v ** pts_to v s ** pure (res == Seq.index s (SZ.v i)))

val write_ref (#a:Type0) (r:R.ref (vec a))
  (i:SZ.t)
  (x:a)
  (#v:erased (vec a))
  (#s:erased (Seq.seq a) { SZ.v i < Seq.length s})
  : stt unit
    (requires R.pts_to r v ** pts_to v s)
    (ensures fun _ -> R.pts_to r v ** pts_to v (Seq.upd s (SZ.v i) x))

val replace_i (#a:Type0) (v:vec a) (i:SZ.t) (x:a)
  (#s:erased (Seq.seq a) { SZ.v i < Seq.length s})
  : stt a
    (requires pts_to v s)
    (ensures fun res -> pts_to v (Seq.upd s (SZ.v i) x) ** pure (res == Seq.index s (SZ.v i)))

val replace_i_ref (#a:Type0) (r:R.ref (vec a)) (i:SZ.t) (x:a)
  (#v:erased (vec a))
  (#s:erased (Seq.seq a) { SZ.v i < Seq.length s})
  : stt a
    (requires R.pts_to r v ** pts_to v s)
    (ensures fun res -> R.pts_to r v ** pts_to v (Seq.upd s (SZ.v i) x) ** pure (res == Seq.index s (SZ.v i)))

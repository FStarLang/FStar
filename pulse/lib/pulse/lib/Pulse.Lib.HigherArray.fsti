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

module Pulse.Lib.HigherArray
open FStar.Tactics.V2
open Pulse.Lib.Core
open Pulse.Class.PtsTo
open PulseCore.FractionalPermission
open FStar.Ghost
module SZ = FStar.SizeT
module Seq = FStar.Seq

val array ([@@@strictly_positive] a:Type u#1) : Type u#0

val length (#a:Type) (x:array a) : Ghost nat (requires True) (ensures SZ.fits)

type elseq (a:Type) (l:SZ.t) = s:erased (Seq.seq a) { Seq.length s == SZ.v l }

type larray t (n:nat) = a:array t { length a == n }

val is_full_array (#a:Type) (x:array a) : prop

val pts_to (#a:Type) ([@@@mkey]x:array a) (#[exact (`1.0R)] p:perm) (s: Seq.seq a) : slprop

[@@pulse_unfold]
instance has_pts_to_array (a:Type u#1) : has_pts_to (array a) (Seq.seq a) = {
  pts_to = pts_to;
}
[@@pulse_unfold]
instance has_pts_to_larray (a:Type u#1) (n : nat) : has_pts_to (larray a n) (Seq.seq a) = {
  pts_to = pts_to;
}

val pts_to_timeless (#a:Type) (x:array a) (p:perm) (s:Seq.seq a)
  : Lemma (timeless (pts_to x #p s))
          [SMTPat (timeless (pts_to x #p s))]

val pts_to_len (#t:Type) (a:array t) (#p:perm) (#x:Seq.seq t)
    : stt_ghost unit emp_inames
          (pts_to a #p x)
          (fun _ → pts_to a #p x ** pure (length a == Seq.length x))

val alloc 
        (#elt: Type)
        (x: elt)
        (n: SZ.t)
  : stt (array elt) 
        (requires emp)
        (ensures fun a ->
            pts_to a (Seq.create (SZ.v n) x) **
            pure (length a == SZ.v n /\ is_full_array a))

(* Written x.(i) *)
val op_Array_Access
        (#t: Type)
        (a: array t)
        (i: SZ.t)
        (#p: perm)
        (#s: Ghost.erased (Seq.seq t){SZ.v i < Seq.length s})
  : stt t
        (requires
            pts_to a #p s)
        (ensures fun res ->
            pts_to a #p s **
            pure (res == Seq.index s (SZ.v i)))


(* Written x.(i) <- v *)
val op_Array_Assignment
        (#t: Type)
        (a: array t)
        (i: SZ.t)
        (v: t)
        (#s: Ghost.erased (Seq.seq t) {SZ.v i < Seq.length s})
  : stt unit
        (requires
            pts_to a s)
        (ensures fun res ->
            pts_to a (Seq.upd s (SZ.v i) v))

val free
        (#elt: Type)
        (a: array elt)
        (#s: Ghost.erased (Seq.seq elt))
  : stt unit
        (requires
            pts_to a s **
            pure (is_full_array a))
        (ensures fun _ ->
            emp)

val share
  (#a:Type)
  (arr:array a)
  (#s:Ghost.erased (Seq.seq a))
  (#p:perm)
  : stt_ghost unit emp_inames
      (requires pts_to arr #p s)
      (ensures fun _ -> pts_to arr #(p /. 2.0R) s ** pts_to arr #(p /. 2.0R) s)

[@@allow_ambiguous]
val gather
  (#a:Type)
  (arr:array a)
  (#s0 #s1:Ghost.erased (Seq.seq a))
  (#p0 #p1:perm)
  : stt_ghost unit emp_inames
      (requires pts_to arr #p0 s0 ** pts_to arr #p1 s1)
      (ensures fun _ -> pts_to arr #(p0 +. p1) s0 ** pure (s0 == s1))

val pts_to_range
  (#a:Type)
  ([@@@mkey]x:array a)
  ([@@@mkey] i [@@@mkey] j : nat)
  (#[exact (`1.0R)] p:perm)
  (s : Seq.seq a) : slprop

val pts_to_range_timeless (#a:Type) (x:array a) (i j : nat) (p:perm) (s:Seq.seq a)
  : Lemma (timeless (pts_to_range x i j #p s))
          [SMTPat (timeless (pts_to_range x i j #p s))]

val pts_to_range_prop
  (#elt: Type) (a: array elt) (#i #j: nat)
  (#p: perm)
  (#s: Seq.seq elt)
: stt_ghost unit emp_inames
    (pts_to_range a i j #p s)
    (fun _ -> pts_to_range a i j #p s ** pure (
      (i <= j /\ j <= length a /\ eq2 #nat (Seq.length s) (j - i))
    ))

val pts_to_range_intro
  (#elt: Type)
  (a: array elt)
  (p: perm)
  (s: Seq.seq elt)
: stt_ghost unit emp_inames
    (pts_to a #p s)
    (fun _ -> pts_to_range a 0 (length a) #p s)

val pts_to_range_elim
  (#elt: Type)
  (a: array elt)
  (p: perm)
  (s: Seq.seq elt)
: stt_ghost unit emp_inames
    (pts_to_range a 0 (length a) #p s)
    (fun _ -> pts_to a #p s)

val pts_to_range_split
  (#elt: Type)
  (a: array elt)
  (i m j: nat)
  (#p: perm)
  (#s: Seq.seq elt)
: stt_ghost unit emp_inames
    (pts_to_range a i j #p s **
      pure (i <= m /\ m <= j)
    )
    (fun _ -> exists* s1 s2.
      pts_to_range a i m #p s1 **
      pts_to_range a m j #p s2 **
      pure (
        i <= m /\ m <= j /\ j <= length a /\
        Seq.length s == j - i /\
        s1 == Seq.slice s 0 (m - i) /\
        s2 == Seq.slice s (m - i) (Seq.length s) /\
        s == Seq.append s1 s2
    ))

val pts_to_range_join
  (#elt: Type)
  (a: array elt)
  (i m j: nat)
  (#p: perm)
  (#s1 #s2: Seq.seq elt)
: stt_ghost unit emp_inames
    (pts_to_range a i m #p s1 ** pts_to_range a m j #p s2)
    (fun _ -> pts_to_range a i j #p (s1 `Seq.append` s2))

val pts_to_range_index
  (#t: Type)
  (a: array t)
  (i: SZ.t)
  (#l: Ghost.erased nat{l <= SZ.v i})
  (#r: Ghost.erased nat{SZ.v i < r})
  (#s: Ghost.erased (Seq.seq t))
  (#p: perm)
: stt t
    (requires
      pts_to_range a l r #p s)
    (ensures fun res ->
      pts_to_range a l r #p s **
      pure (Seq.length s == r - l /\
            res == Seq.index s (SZ.v i - l)))

val pts_to_range_upd
  (#t: Type)
  (a: array t)
  (i: SZ.t)
  (v: t)
  (#l: Ghost.erased nat{l <= SZ.v i})
  (#r: Ghost.erased nat{SZ.v i < r})
  (#s0: Ghost.erased (Seq.seq t))
: stt unit
    (requires pts_to_range a l r s0)
    (ensures fun _ ->
      exists* s.
        pts_to_range a l r s **
        pure(
          Seq.length s0 == r - l /\ s == Seq.upd s0 (SZ.v i - l) v
        ))

val pts_to_range_share
  (#a:Type)
  (arr:array a)
  (#l #r: nat)
  (#s:Seq.seq a)
  (#p:perm)
: stt_ghost unit emp_inames
      (requires pts_to_range arr l r #p s)
      (ensures fun _ -> pts_to_range arr l r #(p /. 2.0R) s ** pts_to_range arr l r #(p /. 2.0R) s)

[@@allow_ambiguous]
val pts_to_range_gather
  (#a:Type)
  (arr:array a)
  (#l #r: nat)
  (#s0 #s1: Seq.seq a)
  (#p0 #p1:perm)
: stt_ghost unit emp_inames
      (requires pts_to_range arr l r #p0 s0 ** pts_to_range arr l r #p1 s1)
      (ensures fun _ -> pts_to_range arr l r #(p0 +. p1) s0 ** pure (s0 == s1))

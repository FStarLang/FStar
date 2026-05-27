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
open Pulse.Class.PtsTo

module SZ = FStar.SizeT
module Seq = FStar.Seq
module T = FStar.Tactics.V2

module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array.Basic

val vec ([@@@strictly_positive] a:Type0) : Type u#0

val length (#a:Type u#0) (x:vec a) : Ghost nat (requires True) (ensures SZ.fits)

inline_for_extraction
type lvec (a:Type0) (n:nat) = v:vec a { length v == n }

val is_full_vec (#a:Type0) (v:vec a) : prop

val pts_to
  (#a:Type0)
  ([@@@mkey] v:vec a)
  (#[T.exact (`1.0R)] p:perm)
  (s:Seq.seq a)
: slprop

[@@pulse_unfold]
instance has_pts_to_vec (a:Type u#0) : has_pts_to (vec a) (Seq.seq a) = { pts_to; }
[@@pulse_unfold]
instance has_pts_to_lvec (a:Type u#0) (n : nat) : has_pts_to (lvec a n) (Seq.seq a) = { pts_to; }

val pts_to_timeless (#a:Type0) (v:vec a) (p:perm) (s:Seq.seq a)
  : Lemma (timeless (pts_to v #p s))
          [SMTPat (timeless (pts_to v #p s))]

ghost
fn pts_to_len (#a:Type0) (v:vec a) (#p:perm) (#s:Seq.seq a)
  preserves pts_to v #p s
  ensures pure (length v == Seq.length s)

fn alloc 
  (#a:Type0)
  (x:a)
  (n:SZ.t)
  returns  v:vec a
  ensures pts_to v (Seq.create (SZ.v n) x) **
          pure (length v == SZ.v n /\ is_full_vec v)

(* Written x.(i) *)
fn op_Array_Access
  (#a: Type0)
  (v:vec a)
  (i:SZ.t)
  (#p:perm)
  (#s:Ghost.erased (Seq.seq a) { SZ.v i < Seq.length s })
  requires pts_to v #p s
  returns  res : a
  ensures  pts_to v #p s **
           rewrites_to res (Seq.index s (SZ.v i))

(* Written x.(i) <- v *)
fn op_Array_Assignment
  (#a:Type0)
  (v:vec a)
  (i:SZ.t)
  (x:a)
  (#s:Ghost.erased (Seq.seq a) { SZ.v i < Seq.length s })
  requires pts_to v s
  ensures  exists* s'. pts_to v s' ** pure (s' == Seq.upd s (SZ.v i) x)

fn free
  (#a:Type0)
  (v:vec a)
  (#s:Ghost.erased (Seq.seq a))
  requires pts_to v s
  requires pure (is_full_vec v)
ghost
fn share
  (#a:Type)
  (v:vec a)
  (#s:Ghost.erased (Seq.seq a))
  (#p:perm)
  requires pts_to v #p s
  ensures pts_to v #(p /. 2.0R) s
  ensures pts_to v #(p /. 2.0R) s

[@@allow_ambiguous]
ghost
fn gather
  (#a:Type)
  (v:vec a)
  (#s0 #s1:Ghost.erased (Seq.seq a))
  (#p0 #p1:perm)
  requires pts_to v #p0 s0
  requires pts_to v #p1 s1
  ensures pts_to v #(p0 +. p1) s0
  ensures pure (s0 == s1)

val vec_to_array (#a:Type0) (v:vec a) : arr:A.array a { A.length arr == length v }

ghost
fn to_array_pts_to (#a:Type0) (v:vec a) (#p:perm) (#s:Seq.seq a)
  requires pts_to v #p s
  ensures A.pts_to (vec_to_array v) #p s

ghost
fn to_vec_pts_to (#a:Type0) (v:vec a) (#p:perm) (#s:Seq.seq a)
  requires A.pts_to (vec_to_array v) #p s
  ensures pts_to v #p s

fn read_ref (#a:Type0) (r:R.ref (vec a))
  (i:SZ.t)
  (#v:erased (vec a))
  (#s:erased (Seq.seq a) { SZ.v i < Seq.length s})
  preserves R.pts_to r v
  preserves pts_to v s
  returns res : a
  ensures pure (res == Seq.index s (SZ.v i))

fn write_ref (#a:Type0) (r:R.ref (vec a))
  (i:SZ.t)
  (x:a)
  (#v:erased (vec a))
  (#s:erased (Seq.seq a) { SZ.v i < Seq.length s})
  preserves R.pts_to r v
  requires pts_to v s
  ensures pts_to v (Seq.upd s (SZ.v i) x)

fn replace_i (#a:Type0) (v:vec a) (i:SZ.t) (x:a)
  (#s:erased (Seq.seq a) { SZ.v i < Seq.length s})
  requires pts_to v s
  returns  res : a
  ensures pts_to v (Seq.upd s (SZ.v i) x)
  ensures pure (res == Seq.index s (SZ.v i))

fn replace_i_ref (#a:Type0) (r:R.ref (vec a)) (i:SZ.t) (x:a)
  (#v:erased (vec a))
  (#s:erased (Seq.seq a) { SZ.v i < Seq.length s})
  preserves R.pts_to r v
  requires pts_to v s
  returns  res : a
  ensures pts_to v (Seq.upd s (SZ.v i) x)
  ensures pure (res == Seq.index s (SZ.v i))

fn compare
        (#t:eqtype)
        (l:SZ.t)
        (a1 a2:lvec t (SZ.v l))
        (#p1 #p2:perm)
        (#s1 #s2:Ghost.erased (Seq.seq t))
  requires
     pts_to a1 #p1 s1 **
     pts_to a2 #p2 s2
  returns res : bool
  ensures
     pts_to a1 #p1 s1 **
     pts_to a2 #p2 s2 **
     pure (res <==> Seq.equal s1 s2)

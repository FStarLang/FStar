(*
   Copyright 2025 Microsoft Research

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

module Pulse.Lib.Array.PtsTo
#lang-pulse
open FStar.Tactics.V2
open Pulse.Lib.Core
open Pulse.Main
open Pulse.Class.PtsTo
open PulseCore.FractionalPermission
open FStar.Ghost
module SZ = FStar.SizeT
module Seq = FStar.Seq
open Pulse.Lib.Array.Core
open Pulse.Lib.SmallType
open Pulse.Lib.Send

val pts_to (#a:Type u#a) ([@@@mkey]x:array a) (#[exact (`1.0R)] p:perm) (s: Seq.seq a) : slprop

[@@pulse_unfold]
instance has_pts_to_array (a:Type u#a) : has_pts_to (array a) (Seq.seq a) = {
  pts_to = pts_to;
}
[@@pulse_unfold]
instance has_pts_to_larray (a:Type u#a) (n : nat) : has_pts_to (larray a n) (Seq.seq a) = {
  pts_to = pts_to;
}

instance val is_send_pts_to #a r #p n : is_send (pts_to #a r #p n)

ghost fn to_mask u#a (#t: Type u#a) (arr: array t) #f (#v: erased _)
  requires arr |-> Frac f v
  ensures exists* (s: Seq.seq (option t)).
    pts_to_mask arr #f s (fun _ -> True) **
    pure (Seq.length s == Seq.length v /\
      (forall (i: nat). i < Seq.length s ==>
        Seq.index s i == Some (Seq.index v i)))

ghost fn from_mask u#a (#t: Type u#a) (arr: array t) #f #v #mask
  requires pts_to_mask arr #f v mask
  requires pure (forall (i: nat). i < Seq.length v ==> mask i /\ Some? (Seq.index v i))
  ensures exists* (v': Seq.seq t).
    arr |-> Frac f v' **
    pure (Seq.length v' == Seq.length v /\
      (forall (i: nat). i < Seq.length v' ==>
        Some (Seq.index v' i) == Seq.index v i))

val pts_to_timeless (#a: Type u#a) (x:array a) (p:perm) (s:Seq.seq a)
  : Lemma (timeless (pts_to x #p s))
          [SMTPat (timeless (pts_to x #p s))]

ghost
fn pts_to_len u#a (#t: Type u#a) (a:array t) (#p:perm) (#x:Seq.seq t)
  preserves pts_to a #p x
  ensures pure (length a == Seq.length x)

ghost
fn pts_to_not_null u#a (#a: Type u#a) (#p:_) (r:array a) (#v:Seq.seq a)
  preserves r |-> Frac p v
  ensures  pure (not (is_null #a r))

[@@deprecated "Array.alloc is unsound; only use for model implementations"]
fn alloc
        u#a (#elt: Type u#a) {| small_type u#a |}
        (x: elt)
        (n: SZ.t)
  returns  a : array elt
  ensures  pts_to a (Seq.create (SZ.v n) x) **
           pure (length a == SZ.v n /\ is_full_array a)

(* Written x.(i) *)
inline_for_extraction
fn op_Array_Access
        u#a (#t: Type u#a)
        (a: array t)
        (i: SZ.t)
        (#p: perm)
        (#s: Ghost.erased (Seq.seq t){SZ.v i < Seq.length s})
  requires pts_to a #p s
  returns  res : t
  ensures  pts_to a #p s **
           rewrites_to res (Seq.index s (SZ.v i))

(* Written x.(i) <- v *)
inline_for_extraction
fn op_Array_Assignment
        u#a (#t: Type u#a)
        (a: array t)
        (i: SZ.t)
        (v: t)
        (#s: Ghost.erased (Seq.seq t) {SZ.v i < Seq.length s})
  requires pts_to a s
  ensures  exists* s'. pts_to a s' ** pure (s' == Seq.upd s (SZ.v i) v)

[@@deprecated "Array.free is unsound; only use for model implementations"]
inline_for_extraction
fn free
        u#a (#elt: Type u#a)
        (a: array elt)
        (#s: Ghost.erased (Seq.seq elt))
  requires pts_to a s
  requires pure (is_full_array a)

ghost
fn share
  u#a (#a: Type u#a)
  (arr:array a)
  (#s:Ghost.erased (Seq.seq a))
  (#p:perm)
  requires pts_to arr #p s
  ensures pts_to arr #(p /. 2.0R) s
  ensures pts_to arr #(p /. 2.0R) s

[@@allow_ambiguous]
ghost
fn gather
  u#a (#a: Type u#a)
  (arr:array a)
  (#s0 #s1:Ghost.erased (Seq.seq a))
  (#p0 #p1:perm)
  requires pts_to arr #p0 s0
  requires pts_to arr #p1 s1
  ensures pts_to arr #(p0 +. p1) s0
  ensures pure (s0 == s1)

[@@allow_ambiguous]
ghost
fn pts_to_injective_eq
    u#a (#a: Type u#a)
    (#p0 #p1:perm)
    (#s0 #s1:Seq.seq a)
    (arr:array a)
  preserves pts_to arr #p0 s0
  preserves pts_to arr #p1 s1
  ensures pure (s0 == s1)

ghost
fn pts_to_perm_bound u#a (#a: Type u#a) (#p:_) (arr: array a) (#s:Seq.seq a)
  preserves pts_to arr #p s
  requires pure (Seq.length s > 0)
  ensures pure (p <=. 1.0R)

fn with_local u#a
  (#a:Type0)
  (init:a)
  (len:SZ.t)
  (#pre:slprop)
  (ret_t:Type u#a)
  (#post:ret_t -> slprop)
  (body:(arr:array a) -> stt ret_t (pre **
                                    (pts_to arr (Seq.create (SZ.v len) init) **
                                     (pure (is_full_array arr) **
                                      pure (length arr == SZ.v len))))
                                   (fun r -> post r ** (exists* v. pts_to arr v)))
  requires pre
  returns r: ret_t
  ensures post r
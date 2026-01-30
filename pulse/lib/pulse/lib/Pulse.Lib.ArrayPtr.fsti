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

module Pulse.Lib.ArrayPtr
#lang-pulse
open FStar.Tactics.V2
open Pulse.Lib.Pervasives
module SZ = FStar.SizeT
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference

(*
The `ArrayPtr.ptr t` type in this module cannot be extracted to Rust
because of the `split` operation, which assumes that the same pointer
can point to either the large subarray or its sub-subarray, depending on the permission.
Rust slices have the length baked in, so they cannot support this operation
without modifying the pointer.

Use `Pulse.Lib.Slice.slice` instead when possible.
*)

val base_t ([@@@strictly_positive] t: Type0) : Tot Type0
val ptr ([@@@strictly_positive] elt: Type0) : Type0

val base #t (p: ptr t) : GTot (base_t t)
val offset #t (p: ptr t) : GTot nat

val null #t : ptr t

val g_is_null #t (p: ptr t) : Ghost bool
  (requires True)
  (ensures fun res -> res == true <==> p == null)

val pts_to
  (#t:Type)
  ([@@@mkey]s:ptr t)
  (#[exact (`1.0R)] p:perm)
  (v : Seq.seq t)
  : slprop

val pts_to_not_null
  (#t:Type)
  (s:ptr t)
  (#p:perm)
  (#v : Seq.seq t)
: stt_ghost unit emp_inames
  (pts_to s #p v)
  (fun _ -> pts_to s #p v ** pure (not (g_is_null s)))

let pts_to_or_null
  (#t: Type)
  ([@@@mkey]s:ptr t)
  (#[exact (`1.0R)] p:perm)
  (v : Seq.seq t)
: slprop
= if g_is_null s then emp else pts_to s #p v

val is_null
  (#t:Type)
  (s:ptr t)
  (#p:perm)
  (#v : Ghost.erased (Seq.seq t))
: stt bool
  (pts_to_or_null s #p v)
  (fun res -> pts_to_or_null s #p v ** pure (res == g_is_null s))

[@@pulse_unfold]
instance has_pts_to_array_ptr (t: Type) : has_pts_to (ptr t) (Seq.seq t) = {
  pts_to = (fun s #p v -> pts_to s #p v);
}

val pts_to_timeless (#a:Type) (x:ptr a) (p:perm) (s:Seq.seq a)
  : Lemma (timeless (pts_to x #p s))
          [SMTPat (timeless (pts_to x #p s))]

val is_from_array (#t: Type) ([@@@mkey]s: ptr t) (sz: nat) (a: A.array t) : slprop

val from_array (#t: Type) (a: A.array t) (#p: perm) (#v: Ghost.erased (Seq.seq t)) : stt (ptr t)
    (A.pts_to a #p v)
    (fun s -> pts_to s #p v ** is_from_array s (Seq.length v) a)

val to_array (#t: Type) (s: ptr t) (a: array t) (#p: perm) (#v: Seq.seq t) : stt_ghost unit emp_inames
    (pts_to s #p v ** is_from_array s (Seq.length v) a)
    (fun _ -> A.pts_to a #p v)

val is_from_ref (#t: Type) ([@@@mkey]s: ptr t) (a: ref t) : slprop

val from_ref (#t: Type) (a: ref t) (#p: perm) (#v: Ghost.erased (t)) : stt (ptr t)
    (R.pts_to a #p v)
    (fun s -> pts_to s #p (Seq.create 1 (Ghost.reveal v)) ** is_from_ref s a)

inline_for_extraction noextract [@@noextract_to "krml"]
let to_ref_t (t: Type) = (s: ptr t) -> (a: ref t) -> (#p: perm) -> (#v: Seq.seq t) -> stt_ghost unit emp_inames
    (pts_to s #p v ** is_from_ref s a ** pure (Seq.length v == 1))
    (fun _ -> exists* v' . R.pts_to a #p v' ** pure (Seq.length v == 1 /\ v' == Seq.index v 0))

val to_ref (#t: Type) : to_ref_t t

val is_as_ref (#t: Type) ([@@@mkey]s: ptr t) (p: perm) (a: ref t) : slprop

inline_for_extraction noextract [@@noextract_to "krml"]
let as_ref_t (t: Type) = (s: ptr t) -> (#p: perm) -> (#v: Seq.seq t) -> stt (R.ref t)
    (pts_to s #p v ** pure (Seq.length v == 1))
    (fun a -> exists* v' . R.pts_to a #p v' ** is_as_ref s p a ** pure (Seq.length v == 1 /\ v' == Seq.index v 0))

val as_ref (#t: Type) : as_ref_t t

val return_as_ref (#t: Type) (a: ref t) (#p: perm) (#v:t) (#s: ptr t) : stt_ghost unit emp_inames
    (R.pts_to a #p v ** is_as_ref s p a)
    (fun _ -> pts_to s #p (Seq.create 1 (Ghost.reveal v)))

(* Written x.(i) *)
fn op_Array_Access
        (#t: Type)
        (a: ptr t)
        (i: SZ.t)
        (#p: perm)
        (#s: Ghost.erased (Seq.seq t))
  requires
     pts_to a #p s **
     pure (SZ.v i < Seq.length s)
  returns res : t
  ensures
     pts_to a #p s **
     pure (SZ.v i < Seq.length s /\
           res == Seq.index s (SZ.v i))

(* Written a.(i) <- v *)
fn op_Array_Assignment
        (#t: Type)
        (a: ptr t)
        (i: SZ.t)
        (v: t)
        (#s: Ghost.erased (Seq.seq t))
  requires pts_to a s
  requires pure (SZ.v i < Seq.length s)
  ensures
    exists* s' .
      pts_to a s' **
      pure (SZ.v i < Seq.length s /\
        s' == Seq.upd s (SZ.v i) v
      )

ghost
fn share
  (#a:Type)
  (arr:ptr a)
  (#s:Ghost.erased (Seq.seq a))
  (#p:perm)
  requires pts_to arr #p s
  ensures  pts_to arr #(p /. 2.0R) s ** pts_to arr #(p /. 2.0R) s

[@@allow_ambiguous]
ghost
fn gather
  (#a:Type)
  (arr:ptr a)
  (#s0 #s1:Ghost.erased (Seq.seq a))
  (#p0 #p1:perm)
  requires pts_to arr #p0 s0
  requires pts_to arr #p1 s1
  requires pure (Seq.length s0 == Seq.length s1)
  ensures  pts_to arr #(p0 +. p1) s0 ** pure (s0 == s1)


let adjacent #t (a: ptr t) (sz: nat) (b: ptr t) : prop =
  base a == base b /\ offset a + sz == offset b

fn split (#t: Type) (s: ptr t) (#p: perm) (i: SZ.t)
  (#v: Ghost.erased (Seq.seq t) { SZ.v i <= Seq.length v })
  requires pts_to s #p v
  returns  s' : ptr t
  ensures
      pts_to s #p (Seq.slice v 0 (SZ.v i)) **
      pts_to s' #p (Seq.slice v (SZ.v i) (Seq.length v)) **
      pure (adjacent s (SZ.v i) s')

ghost
fn ghost_split (#t: Type) (s: ptr t) (#p: perm) (i: SZ.t)
  (#v: Ghost.erased (Seq.seq t) { SZ.v i <= Seq.length v })
  requires pts_to s #p v
  returns s' : erased (ptr t)
  ensures
      pts_to s #p (Seq.slice v 0 (SZ.v i)) **
      pts_to (reveal s') #p (Seq.slice v (SZ.v i) (Seq.length v)) **
      pure (adjacent s (SZ.v i) s')

ghost
fn join (#t: Type) (s1: ptr t) (#p: perm) (#v1: Seq.seq t) (s2: ptr t) (#v2: Seq.seq t)
  requires pts_to s1 #p v1
  requires pts_to s2 #p v2
  requires pure (adjacent s1 (Seq.length v1) s2)
  ensures  pts_to s1 #p (Seq.append v1 v2)

fn memcpy
    (#t:Type0) (#p0:perm)
    (src:ptr t) (idx_src: SZ.t)
    (dst:ptr t) (idx_dst: SZ.t)
    (len: SZ.t)
    (#s0:Ghost.erased (Seq.seq t) { SZ.v idx_src + SZ.v len <= Seq.length s0 })
    (#s1:Ghost.erased (Seq.seq t) { SZ.v idx_dst + SZ.v len <= Seq.length s1 })
  requires pts_to src #p0 s0
  requires pts_to dst s1
  ensures  pts_to src #p0 s0 ** pts_to dst (Seq.slice s0 0 (SZ.v len) `Seq.append` Seq.slice s1 (SZ.v len) (Seq.length s1))

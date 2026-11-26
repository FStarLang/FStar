(*
   Copyright 2026 Microsoft Research

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

(* The OCaml implementation of Pulse.Lib.Atomic.

   This is Pulse.Lib.Atomic-model.fst with Custard externs: both
   [atomic_ref t] and [atomic_box t] are OCaml's [t Atomic.t], and the
   operations are those of the [Atomic] module.  The bodies are the
   sequential model; they check the specifications but are not extracted.

   OCaml's [Atomic.compare_and_set] compares physically, while
   [compare_exchange] compares values, which may be boxed (e.g. [UInt64.t]):
   so it loops, reading the current value and trying to replace it if it
   is structurally equal to [expected].  The read-modify-write operations
   are a similar loop. *)
module Pulse.Lib.Atomic
#lang-pulse

open Pulse.Lib.Core
open Pulse.Lib.Send
open PulseCore.FractionalPermission
open FStar.Ghost
open Pulse.Class.PtsTo
module R = Pulse.Lib.Reference
module B = Pulse.Lib.Box
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I8 = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64
module SZ = FStar.SizeT

let is_atomic_base t =
  t == bool \/
  t == U8.t \/ t == U16.t \/ t == U32.t \/ t == U64.t \/
  t == I8.t \/ t == I16.t \/ t == I32.t \/ t == I64.t \/
  t == SZ.t
let is_atomic_base_intro () = ()

let is_atomic_uint t add_mod sub_mod logand logor logxor =
  (t == U8.t /\ (forall (x y: t).
     add_mod x y == U8.add_mod x y /\ sub_mod x y == U8.sub_mod x y /\ logand x y == U8.logand x y /\ logor x y == U8.logor x y /\ logxor x y == U8.logxor x y)) \/
  (t == U16.t /\ (forall (x y: t).
     add_mod x y == U16.add_mod x y /\ sub_mod x y == U16.sub_mod x y /\ logand x y == U16.logand x y /\ logor x y == U16.logor x y /\ logxor x y == U16.logxor x y)) \/
  (t == U32.t /\ (forall (x y: t).
     add_mod x y == U32.add_mod x y /\ sub_mod x y == U32.sub_mod x y /\ logand x y == U32.logand x y /\ logor x y == U32.logor x y /\ logxor x y == U32.logxor x y)) \/
  (t == U64.t /\ (forall (x y: t).
     add_mod x y == U64.add_mod x y /\ sub_mod x y == U64.sub_mod x y /\ logand x y == U64.logand x y /\ logor x y == U64.logor x y /\ logxor x y == U64.logxor x y))
let is_atomic_uint_intro () = ()


let atomic_t t = t
let to_atomic x = x
let of_atomic x = x
let of_to_atomic _ = ()
let to_of_atomic _ = ()

[@@custard_extern "Atomic.t"]
let atomic_ref t = R.ref (atomic_t t)

let pts_to #t r #p v = R.pts_to r #p (to_atomic v)

let is_send_pts_to r v = Tactics.Typeclasses.solve

let pts_to_timeless r p v = ()

ghost
fn share (#t: Type0) (r: atomic_ref t) (#v: erased t) (#p: perm)
  requires r |-> Frac p v
  ensures  r |-> Frac (p /. 2.0R) v
  ensures  r |-> Frac (p /. 2.0R) v
{
  unfold pts_to r #p v;
  R.share r;
  fold pts_to r #(p /. 2.0R) v;
  fold pts_to r #(p /. 2.0R) v;
}

[@@allow_ambiguous]
ghost
fn gather (#t: Type0) (r: atomic_ref t) (#v0 #v1: erased t) (#p0 #p1: perm)
  requires r |-> Frac p0 v0
  requires r |-> Frac p1 v1
  ensures  r |-> Frac (p0 +. p1) v0
  ensures  pure (v0 == v1)
{
  unfold pts_to r #p0 v0;
  unfold pts_to r #p1 v1;
  R.gather r;
  fold pts_to r #(p0 +. p1) v0;
}

ghost
fn pts_to_perm_bound (#t: Type0) (r: atomic_ref t) (#p: perm) (#v: t)
  preserves r |-> Frac p v
  ensures   pure (p <=. 1.0R)
{
  unfold pts_to r #p v;
  R.pts_to_perm_bound r;
  fold pts_to r #p v;
}

noextract
fn load_seq (#t: Type0) (r: atomic_ref t) (#p: perm) (#v: erased t)
  preserves r |-> Frac p v
  returns  x: t
  ensures  rewrites_to x (reveal v)
{
  unfold pts_to r #p v;
  let x = R.(!r);
  fold pts_to r #p v;
  of_atomic x
}

[@@custard_extern "Atomic.get"]
let load #t #_ r #p #v =
  as_atomic (r |-> Frac p v) (fun (x: t) -> (r |-> Frac p v) ** rewrites_to x (reveal v))
    (load_seq r #p #v)

noextract
fn store_seq (#t: Type0) (r: atomic_ref t) (x: t) (#v: erased t)
  requires r |-> v
  ensures  r |-> x
{
  unfold pts_to r v;
  R.(r := to_atomic x);
  fold pts_to r x;
}

[@@custard_extern "Atomic.set"]
let store #t #_ r x #v =
  as_atomic (r |-> v) (fun (_: unit) -> r |-> x) (store_seq r x #v)

noextract
fn update_seq (#t: Type0) (r: atomic_ref t) (f: t -> t) (#v: erased t)
  requires r |-> v
  returns  y: t
  ensures  r |-> f v
  ensures  rewrites_to y (reveal v)
{
  unfold pts_to r v;
  let y = of_atomic R.(!r);
  R.(r := to_atomic (f y));
  fold pts_to r (f v);
  y
}

[@@custard_extern "(fun r f -> let rec go () = let c = Atomic.get r in if Atomic.compare_and_set r c (f c) then c else go () in go ())"]
let update (#t: Type0) (r: atomic_ref t) (f: t -> t) (#v: erased t)
  : stt_atomic t #PulseCore.Observability.Observable emp_inames (r |-> v)
      (fun y -> (r |-> f v) ** rewrites_to y (reveal v))
  = as_atomic (r |-> v) (fun (y: t) -> (r |-> f v) ** rewrites_to y (reveal v)) (update_seq r f #v)

[@@custard_extern "Atomic.exchange"]
let exchange #t #_ r x #v = update r (fun _ -> x) #v

noextract
fn compare_exchange_seq (#t: Type0) {| d: atomic_base t |} (r: atomic_ref t) (expected desired: t) (#v: erased t)
  requires r |-> v
  returns  b: bool
  ensures  (if b then (r |-> desired) ** pure (reveal v == expected)
             else (r |-> v) ** pure (reveal v =!= expected))
{
  unfold pts_to r v;
  let y = of_atomic R.(!r);
  let _ : squash (hasEq t) = d.atomic_base_has_eq;
  if (y = expected) {
    R.(r := to_atomic desired);
    fold pts_to r desired;
    true
  } else {
    fold pts_to r v;
    false
  }
}

[@@custard_extern "(fun r expected desired -> let rec go () = let c = Atomic.get r in if c = expected then (Atomic.compare_and_set r c desired || go ()) else false in go ())"]
let compare_exchange #t #d r expected desired #v =
  as_atomic (r |-> v)
    (fun (b: bool) -> if b then (r |-> desired) ** pure (reveal v == expected)
                      else (r |-> v) ** pure (reveal v =!= expected))
    (compare_exchange_seq #t #d r expected desired #v)

let fetch_add #t #_ r x #v = update r (fun y -> add_mod y x) #v
let fetch_sub #t #_ r x #v = update r (fun y -> sub_mod y x) #v
let fetch_and #t #_ r x #v = update r (fun y -> logand y x) #v
let fetch_or  #t #_ r x #v = update r (fun y -> logor y x) #v
let fetch_xor #t #_ r x #v = update r (fun y -> logxor y x) #v

[@@custard_extern "Atomic.t"]
let atomic_box t = B.box (atomic_t t)

let box_pts_to #t b #p v = B.pts_to b #p (to_atomic v)

let is_send_box_pts_to b v = Tactics.Typeclasses.solve

let box_pts_to_timeless b p v = ()

[@@custard_extern "Atomic.make"]
fn alloc_box (#t: Type0) {| atomic_base t |} (x: t)
  returns b: atomic_box t
  ensures b |-> x
{
  let b = B.alloc (to_atomic x);
  fold box_pts_to b x;
  b
}

[@@custard_extern "(fun _ -> ())"]
fn free_box (#t: Type0) (b: atomic_box t) (#v: erased t)
  requires b |-> v
{
  unfold box_pts_to b v;
  B.free b
}

ghost
fn share_box (#t: Type0) (b: atomic_box t) (#v: erased t) (#p: perm)
  requires b |-> Frac p v
  ensures  b |-> Frac (p /. 2.0R) v
  ensures  b |-> Frac (p /. 2.0R) v
{
  unfold box_pts_to b #p v;
  B.share b;
  fold box_pts_to b #(p /. 2.0R) v;
  fold box_pts_to b #(p /. 2.0R) v;
}

[@@allow_ambiguous]
ghost
fn gather_box (#t: Type0) (b: atomic_box t) (#v0 #v1: erased t) (#p0 #p1: perm)
  requires b |-> Frac p0 v0
  requires b |-> Frac p1 v1
  ensures  b |-> Frac (p0 +. p1) v0
  ensures  pure (v0 == v1)
{
  unfold box_pts_to b #p0 v0;
  unfold box_pts_to b #p1 v1;
  B.gather b;
  fold box_pts_to b #(p0 +. p1) v0;
}

ghost
fn box_pts_to_perm_bound (#t: Type0) (b: atomic_box t) (#p: perm) (#v: t)
  preserves b |-> Frac p v
  ensures   pure (p <=. 1.0R)
{
  unfold box_pts_to b #p v;
  B.to_ref_pts_to b;
  R.pts_to_perm_bound (B.box_to_ref b);
  B.to_box_pts_to b;
  fold box_pts_to b #p v;
}

[@@custard_extern "(fun b -> b)"]
let box_to_ref b = B.box_to_ref b

let is_box_ref r = R.is_full_ref r

ghost
fn to_ref_pts_to (#t: Type0) (b: atomic_box t) (#p: perm) (#v: t)
  requires b |-> Frac p v
  ensures  box_to_ref b |-> Frac p v
  ensures  pure (is_box_ref (box_to_ref b))
{
  unfold box_pts_to b #p v;
  B.to_ref_pts_to b;
  fold pts_to (box_to_ref b) #p v;
}

ghost
fn to_box_pts_to (#t: Type0) (b: atomic_box t) (#p: perm) (#v: t)
  requires box_to_ref b |-> Frac p v
  requires pure (is_box_ref (box_to_ref b))
  ensures  b |-> Frac p v
{
  unfold pts_to (box_to_ref b) #p v;
  B.to_box_pts_to b;
  fold box_pts_to b #p v;
}

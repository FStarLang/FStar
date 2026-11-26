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

module Pulse.Lib.Atomic
#lang-pulse

(** Sequentially consistent atomic memory cells.

    There are two kinds of cell, both over a base type [t] (see
    [atomic_base]):

    - [atomic_box t] is a heap-allocated atomic cell, with [alloc_box] and
      [free_box].  This is what portable code should use.

    - [atomic_ref t] is a reference to an atomic cell that someone else
      owns.  Every [atomic_box] can be viewed as an [atomic_ref]
      ([box_to_ref]).  On C, [atomic_ref t] is a pointer to an [atomic_t t],
      so an atomic cell can also be a local variable, an array element or a
      struct field: [Pulse.Lib.Atomic.Ref] converts a [ref (atomic_t t)] to
      an [atomic_ref t].  That module is only available on C.

    All operations are sequentially consistent ([memory_order_seq_cst]).

    Implementations (see doc/ref/targets.md):
    - [Pulse.Lib.Atomic-model.fst] is a sequential model and is never
      extracted.
    - [Pulse.Lib.Atomic-c.fst] (Custard's direct C backend): [atomic_t t] is
      C11's [_Atomic(t)], [atomic_ref t] is [_Atomic(t) *], [atomic_box t]
      is a heap-allocated [_Atomic(t)], and the operations are the C11
      generic functions of [<stdatomic.h>].  The generated C includes
      [Pulse_Lib_Atomic_runtime.h], from [share/pulse/runtime].  It uses GNU C
      statement expressions, so it needs GCC or Clang.
    - [Pulse.Lib.Atomic-ocaml.fst]: both [atomic_ref t] and [atomic_box t]
      are OCaml's [t Atomic.t].  [compare_exchange] compares by value, not
      by physical equality.

    This module supersedes [Pulse.Lib.Primitives]. *)

open Pulse.Lib.Core
open Pulse.Lib.Send
open PulseCore.FractionalPermission
open FStar.Ghost
open Pulse.Class.PtsTo
module T = FStar.Tactics.V2
module R = Pulse.Lib.Reference
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I8 = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64
module SZ = FStar.SizeT

(** {1 Base types} *)

(** The types that atomic cells can hold: [bool], the machine integers up to
    64 bits, and [SizeT.t].  These are lock-free on all mainstream C targets
    and are compared by value (no padding bits).

    The set is closed: [is_atomic_base] is abstract, and only holds of these
    types. *)
val is_atomic_base (t: Type0) : prop

val is_atomic_base_intro (_: unit)
  : Lemma (is_atomic_base bool /\
           is_atomic_base U8.t /\ is_atomic_base U16.t /\
           is_atomic_base U32.t /\ is_atomic_base U64.t /\
           is_atomic_base I8.t /\ is_atomic_base I16.t /\
           is_atomic_base I32.t /\ is_atomic_base I64.t /\
           is_atomic_base SZ.t)

[@@erasable]
class atomic_base (t: Type0) = {
  atomic_base_has_eq : squash (hasEq t);
  atomic_base_ok : squash (is_atomic_base t);
}

let mk_atomic_base (t: eqtype) (_: squash (is_atomic_base t)) : atomic_base t =
  { atomic_base_has_eq = (); atomic_base_ok = () }

instance atomic_base_bool : atomic_base bool = is_atomic_base_intro (); mk_atomic_base bool ()
instance atomic_base_u8   : atomic_base U8.t  = is_atomic_base_intro (); mk_atomic_base U8.t ()
instance atomic_base_u16  : atomic_base U16.t = is_atomic_base_intro (); mk_atomic_base U16.t ()
instance atomic_base_u32  : atomic_base U32.t = is_atomic_base_intro (); mk_atomic_base U32.t ()
instance atomic_base_u64  : atomic_base U64.t = is_atomic_base_intro (); mk_atomic_base U64.t ()
instance atomic_base_i8   : atomic_base I8.t  = is_atomic_base_intro (); mk_atomic_base I8.t ()
instance atomic_base_i16  : atomic_base I16.t = is_atomic_base_intro (); mk_atomic_base I16.t ()
instance atomic_base_i32  : atomic_base I32.t = is_atomic_base_intro (); mk_atomic_base I32.t ()
instance atomic_base_i64  : atomic_base I64.t = is_atomic_base_intro (); mk_atomic_base I64.t ()
instance atomic_base_sizet : atomic_base SZ.t = is_atomic_base_intro (); mk_atomic_base SZ.t ()

(** The unsigned machine integers, which additionally support the
    read-modify-write arithmetic operations ([fetch_add], ...).  The methods
    specify them, with wrap-around semantics.  Again, [is_atomic_uint] is
    abstract, and only holds of the instances below. *)
val is_atomic_uint (t: Type0) (add_mod sub_mod logand logor logxor: t -> t -> t) : prop

val is_atomic_uint_intro (_: unit)
  : Lemma (is_atomic_uint U8.t U8.add_mod U8.sub_mod U8.logand U8.logor U8.logxor /\
           is_atomic_uint U16.t U16.add_mod U16.sub_mod U16.logand U16.logor U16.logxor /\
           is_atomic_uint U32.t U32.add_mod U32.sub_mod U32.logand U32.logor U32.logxor /\
           is_atomic_uint U64.t U64.add_mod U64.sub_mod U64.logand U64.logor U64.logxor)

class atomic_uint (t: Type0) = {
  [@@@FStar.Tactics.Typeclasses.tcinstance]
  uint_base : atomic_base t;
  add_mod : t -> t -> t;
  sub_mod : t -> t -> t;
  logand : t -> t -> t;
  logor : t -> t -> t;
  logxor : t -> t -> t;
  [@@@FStar.Tactics.Typeclasses.no_method]
  atomic_uint_ok : squash (is_atomic_uint t add_mod sub_mod logand logor logxor);
}

instance atomic_uint_u8 : atomic_uint U8.t = is_atomic_uint_intro (); {
  uint_base = atomic_base_u8;
  add_mod = U8.add_mod; sub_mod = U8.sub_mod;
  logand = U8.logand; logor = U8.logor; logxor = U8.logxor;
  atomic_uint_ok = ();
}
instance atomic_uint_u16 : atomic_uint U16.t = is_atomic_uint_intro (); {
  uint_base = atomic_base_u16;
  add_mod = U16.add_mod; sub_mod = U16.sub_mod;
  logand = U16.logand; logor = U16.logor; logxor = U16.logxor;
  atomic_uint_ok = ();
}
instance atomic_uint_u32 : atomic_uint U32.t = is_atomic_uint_intro (); {
  uint_base = atomic_base_u32;
  add_mod = U32.add_mod; sub_mod = U32.sub_mod;
  logand = U32.logand; logor = U32.logor; logxor = U32.logxor;
  atomic_uint_ok = ();
}
instance atomic_uint_u64 : atomic_uint U64.t = is_atomic_uint_intro (); {
  uint_base = atomic_base_u64;
  add_mod = U64.add_mod; sub_mod = U64.sub_mod;
  logand = U64.logand; logor = U64.logor; logxor = U64.logxor;
  atomic_uint_ok = ();
}

(** {1 Atomic values}

    [atomic_t t] is C's [_Atomic(t)]: the type of an atomic object, which may
    live anywhere a [t] may.  It is the same value as a [t]; only the
    accesses differ.  ([atomic] would be the natural name, but it is a Pulse
    keyword.) *)

val atomic_t ([@@@strictly_positive] t: Type0) : Type0

val to_atomic (#t: Type0) (x: t) : atomic_t t

val of_atomic (#t: Type0) (x: atomic_t t) : t

val of_to_atomic (#t: Type0) (x: t)
  : Lemma (of_atomic (to_atomic x) == x)
          [SMTPat (to_atomic x)]

val to_of_atomic (#t: Type0) (x: atomic_t t)
  : Lemma (to_atomic (of_atomic x) == x)
          [SMTPat (of_atomic x)]

(** {1 Atomic references} *)

val atomic_ref ([@@@strictly_positive] t: Type0) : Type0

val pts_to (#t: Type0) ([@@@mkey] r: atomic_ref t) (#[T.exact (`1.0R)] p: perm) (v: t)
  : slprop

[@@pulse_unfold]
instance has_pts_to_atomic_ref (t: Type0) : has_pts_to (atomic_ref t) t = {
  pts_to = pts_to;
}

instance val is_send_pts_to (#t: Type0) (r: atomic_ref t) (#p: perm) (v: t)
  : is_send (pts_to r #p v)

val pts_to_timeless (#t: Type0) ([@@@mkey] r: atomic_ref t) (p: perm) (v: t)
  : Lemma (timeless (pts_to r #p v))
          [SMTPat (timeless (pts_to r #p v))]

ghost
fn share (#t: Type0) (r: atomic_ref t) (#v: erased t) (#p: perm)
  requires r |-> Frac p v
  ensures  r |-> Frac (p /. 2.0R) v
  ensures  r |-> Frac (p /. 2.0R) v

[@@allow_ambiguous]
ghost
fn gather (#t: Type0) (r: atomic_ref t) (#v0 #v1: erased t) (#p0 #p1: perm)
  requires r |-> Frac p0 v0
  requires r |-> Frac p1 v1
  ensures  r |-> Frac (p0 +. p1) v0
  ensures  pure (v0 == v1)

ghost
fn pts_to_perm_bound (#t: Type0) (r: atomic_ref t) (#p: perm) (#v: t)
  preserves r |-> Frac p v
  ensures   pure (p <=. 1.0R)

(** [atomic_load] *)
atomic fn load (#t: Type0) {| atomic_base t |} (r: atomic_ref t) (#p: perm) (#v: erased t)
  preserves r |-> Frac p v
  returns  x: t
  ensures  rewrites_to x (reveal v)

(** [atomic_store] *)
atomic fn store (#t: Type0) {| atomic_base t |} (r: atomic_ref t) (x: t) (#v: erased t)
  requires r |-> v
  ensures  r |-> x

(** [atomic_exchange]: stores [x], returns the previous value. *)
atomic fn exchange (#t: Type0) {| atomic_base t |} (r: atomic_ref t) (x: t) (#v: erased t)
  requires r |-> v
  returns  y: t
  ensures  r |-> x
  ensures  rewrites_to y (reveal v)

(** [atomic_compare_exchange_strong]: if [r] holds [expected], replaces it
    by [desired] and returns [true]; otherwise returns [false].  It is
    *strong*: it fails only if the value differs from [expected]. *)
atomic fn compare_exchange (#t: Type0) {| atomic_base t |} (r: atomic_ref t)
    (expected desired: t) (#v: erased t)
  requires r |-> v
  returns  b: bool
  ensures  (if b then (r |-> desired) ** pure (reveal v == expected)
             else (r |-> v) ** pure (reveal v =!= expected))

(** The read-modify-write operations return the previous value. *)

(** [atomic_fetch_add] (wraps around) *)
atomic fn fetch_add (#t: Type0) {| atomic_uint t |} (r: atomic_ref t) (x: t) (#v: erased t)
  requires r |-> v
  returns  y: t
  ensures  r |-> add_mod v x
  ensures  rewrites_to y (reveal v)

(** [atomic_fetch_sub] (wraps around) *)
atomic fn fetch_sub (#t: Type0) {| atomic_uint t |} (r: atomic_ref t) (x: t) (#v: erased t)
  requires r |-> v
  returns  y: t
  ensures  r |-> sub_mod v x
  ensures  rewrites_to y (reveal v)

(** [atomic_fetch_and] *)
atomic fn fetch_and (#t: Type0) {| atomic_uint t |} (r: atomic_ref t) (x: t) (#v: erased t)
  requires r |-> v
  returns  y: t
  ensures  r |-> logand v x
  ensures  rewrites_to y (reveal v)

(** [atomic_fetch_or] *)
atomic fn fetch_or (#t: Type0) {| atomic_uint t |} (r: atomic_ref t) (x: t) (#v: erased t)
  requires r |-> v
  returns  y: t
  ensures  r |-> logor v x
  ensures  rewrites_to y (reveal v)

(** [atomic_fetch_xor] *)
atomic fn fetch_xor (#t: Type0) {| atomic_uint t |} (r: atomic_ref t) (x: t) (#v: erased t)
  requires r |-> v
  returns  y: t
  ensures  r |-> logxor v x
  ensures  rewrites_to y (reveal v)

(** {1 Atomic boxes} *)

val atomic_box ([@@@strictly_positive] t: Type0) : Type0

val box_pts_to (#t: Type0) ([@@@mkey] b: atomic_box t) (#[T.exact (`1.0R)] p: perm) (v: t)
  : slprop

[@@pulse_unfold]
instance has_pts_to_atomic_box (t: Type0) : has_pts_to (atomic_box t) t = {
  pts_to = box_pts_to;
}

instance val is_send_box_pts_to (#t: Type0) (b: atomic_box t) (#p: perm) (v: t)
  : is_send (box_pts_to b #p v)

val box_pts_to_timeless (#t: Type0) ([@@@mkey] b: atomic_box t) (p: perm) (v: t)
  : Lemma (timeless (box_pts_to b #p v))
          [SMTPat (timeless (box_pts_to b #p v))]

fn alloc_box (#t: Type0) {| atomic_base t |} (x: t)
  returns b: atomic_box t
  ensures b |-> x

fn free_box (#t: Type0) (b: atomic_box t) (#v: erased t)
  requires b |-> v

ghost
fn share_box (#t: Type0) (b: atomic_box t) (#v: erased t) (#p: perm)
  requires b |-> Frac p v
  ensures  b |-> Frac (p /. 2.0R) v
  ensures  b |-> Frac (p /. 2.0R) v

[@@allow_ambiguous]
ghost
fn gather_box (#t: Type0) (b: atomic_box t) (#v0 #v1: erased t) (#p0 #p1: perm)
  requires b |-> Frac p0 v0
  requires b |-> Frac p1 v1
  ensures  b |-> Frac (p0 +. p1) v0
  ensures  pure (v0 == v1)

ghost
fn box_pts_to_perm_bound (#t: Type0) (b: atomic_box t) (#p: perm) (#v: t)
  preserves b |-> Frac p v
  ensures   pure (p <=. 1.0R)

(** Viewing a box as a reference.  The reference is only good for as long as
    the box is not freed: [to_box_pts_to] gives the box back, and
    [is_box_ref] records that the reference came from a box. *)

val box_to_ref (#t: Type0) (b: atomic_box t) : atomic_ref t

val is_box_ref (#t: Type0) (r: atomic_ref t) : prop

ghost
fn to_ref_pts_to (#t: Type0) (b: atomic_box t) (#p: perm) (#v: t)
  requires b |-> Frac p v
  ensures  box_to_ref b |-> Frac p v
  ensures  pure (is_box_ref (box_to_ref b))

ghost
fn to_box_pts_to (#t: Type0) (b: atomic_box t) (#p: perm) (#v: t)
  requires box_to_ref b |-> Frac p v
  requires pure (is_box_ref (box_to_ref b))
  ensures  b |-> Frac p v

(** The operations on boxes, through [box_to_ref]. *)

inline_for_extraction
atomic fn load_box (#t: Type0) {| atomic_base t |} (b: atomic_box t) (#p: perm) (#v: erased t)
  preserves b |-> Frac p v
  returns  x: t
  ensures  rewrites_to x (reveal v)
{
  to_ref_pts_to b;
  let x = load (box_to_ref b);
  to_box_pts_to b;
  x
}

inline_for_extraction
atomic fn store_box (#t: Type0) {| atomic_base t |} (b: atomic_box t) (x: t) (#v: erased t)
  requires b |-> v
  ensures  b |-> x
{
  to_ref_pts_to b;
  store (box_to_ref b) x;
  to_box_pts_to b;
}

inline_for_extraction
atomic fn exchange_box (#t: Type0) {| atomic_base t |} (b: atomic_box t) (x: t) (#v: erased t)
  requires b |-> v
  returns  y: t
  ensures  b |-> x
  ensures  rewrites_to y (reveal v)
{
  to_ref_pts_to b;
  let y = exchange (box_to_ref b) x;
  to_box_pts_to b;
  y
}

inline_for_extraction
atomic fn compare_exchange_box (#t: Type0) {| atomic_base t |} (b: atomic_box t)
    (expected desired: t) (#v: erased t)
  requires b |-> v
  returns  ok: bool
  ensures  (if ok then (b |-> desired) ** pure (reveal v == expected)
             else (b |-> v) ** pure (reveal v =!= expected))
{
  to_ref_pts_to b;
  let ok = compare_exchange (box_to_ref b) expected desired;
  if ok {
    to_box_pts_to b;
    true
  } else {
    to_box_pts_to b;
    false
  }
}

inline_for_extraction
atomic fn fetch_add_box (#t: Type0) {| atomic_uint t |} (b: atomic_box t) (x: t) (#v: erased t)
  requires b |-> v
  returns  y: t
  ensures  b |-> add_mod v x
  ensures  rewrites_to y (reveal v)
{
  to_ref_pts_to b;
  let y = fetch_add (box_to_ref b) x;
  to_box_pts_to b;
  y
}

inline_for_extraction
atomic fn fetch_sub_box (#t: Type0) {| atomic_uint t |} (b: atomic_box t) (x: t) (#v: erased t)
  requires b |-> v
  returns  y: t
  ensures  b |-> sub_mod v x
  ensures  rewrites_to y (reveal v)
{
  to_ref_pts_to b;
  let y = fetch_sub (box_to_ref b) x;
  to_box_pts_to b;
  y
}

inline_for_extraction
atomic fn fetch_and_box (#t: Type0) {| atomic_uint t |} (b: atomic_box t) (x: t) (#v: erased t)
  requires b |-> v
  returns  y: t
  ensures  b |-> logand v x
  ensures  rewrites_to y (reveal v)
{
  to_ref_pts_to b;
  let y = fetch_and (box_to_ref b) x;
  to_box_pts_to b;
  y
}

inline_for_extraction
atomic fn fetch_or_box (#t: Type0) {| atomic_uint t |} (b: atomic_box t) (x: t) (#v: erased t)
  requires b |-> v
  returns  y: t
  ensures  b |-> logor v x
  ensures  rewrites_to y (reveal v)
{
  to_ref_pts_to b;
  let y = fetch_or (box_to_ref b) x;
  to_box_pts_to b;
  y
}

inline_for_extraction
atomic fn fetch_xor_box (#t: Type0) {| atomic_uint t |} (b: atomic_box t) (x: t) (#v: erased t)
  requires b |-> v
  returns  y: t
  ensures  b |-> logxor v x
  ensures  rewrites_to y (reveal v)
{
  to_ref_pts_to b;
  let y = fetch_xor (box_to_ref b) x;
  to_box_pts_to b;
  y
}

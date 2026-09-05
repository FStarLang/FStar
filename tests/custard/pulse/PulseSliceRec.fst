(*
   Copyright 2008-2026 Microsoft Research

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

(* Section 20.6.  A slice held in a *field* rather than passed in an argument.

   [PulseSlice.fst] covers a slice that only ever flows through arguments and
   results, which is the shape karamel's Rust hooks were written against.  A
   struct with a slice field is the other one, and it is what EverParse's
   [cbor_string] and [cbor_array] are: karamel then has to give the struct a
   lifetime parameter, since [&[u8]] cannot appear in a type that binds none.

   Both a record and a variant, because karamel computes the two through
   separate branches of the same fixpoint. *)
module PulseSliceRec
#lang-pulse
open Pulse
open Pulse.Lib.Slice.Util
module A = Pulse.Lib.Array
module S = Pulse.Lib.Slice
module US = FStar.SizeT
module U8 = FStar.UInt8
open Pulse { pts_to }

noeq
type view = {
  bytes: S.slice U8.t;
  tag:   U8.t;
}

noeq
type either_view =
  | Whole of S.slice U8.t
  | Tagged of view

(* EverParse's [cbor_raw]/[cbor_array] in miniature: a variant that reaches
   itself through a slice.  karamel computes a struct's lifetime and box by a
   fixpoint over the fields, and this is the shape that makes the fixpoint
   have to iterate rather than read the answer off one pass. *)
noeq
type tree =
  | Leaf of U8.t
  | Node of node

and node = {
  kids: S.slice tree;
}

(* Section 20.6.  Returned *by value*, which is the case that differs: karamel
   sorts a struct holding pointers into one of two disjoint sets, "returned"
   (own the pointees, so [Box]) and "not returned" (borrow them, so a
   lifetime).  A slice belongs to neither -- it is a borrow by construction
   and cannot be owned -- so a returned struct with a slice field used to get
   [box=true, lifetime=false] and emit [&[u8]] in a type binding no lifetime. *)
let mk_view (b: S.slice U8.t) : view = { bytes = b; tag = 1uy }

(* Reading through the field is what forces the struct to be a real value in
   the generated code rather than something the simplifier can dissolve. *)
fn read_view (v: view) (#s: erased (Seq.seq U8.t))
    requires pts_to v.bytes s ** pure (Seq.length s > 0)
    returns x: U8.t
    ensures pts_to v.bytes s
{
  S.pts_to_len v.bytes;
  let x = v.bytes.(0sz);
  x
}

fn read_either (e: either_view) (#s: erased (Seq.seq U8.t))
    requires (match e with
              | Whole b -> pts_to b s
              | Tagged v -> pts_to v.bytes s) ** pure (Seq.length s > 0)
    returns x: U8.t
    ensures (match e with
             | Whole b -> pts_to b s
             | Tagged v -> pts_to v.bytes s)
{
  match e {
    Whole b -> {
      rewrite (match e with
               | Whole b -> pts_to b s
               | Tagged v -> pts_to v.bytes s) as (pts_to b s);
      S.pts_to_len b;
      let x = b.(0sz);
      rewrite (pts_to b s) as (match e with
                               | Whole b -> pts_to b s
                               | Tagged v -> pts_to v.bytes s);
      x
    }
    Tagged v -> {
      rewrite (match e with
               | Whole b -> pts_to b s
               | Tagged v -> pts_to v.bytes s) as (pts_to v.bytes s);
      S.pts_to_len v.bytes;
      let x = v.bytes.(0sz);
      rewrite (pts_to v.bytes s) as (match e with
                                     | Whole b -> pts_to b s
                                     | Tagged v -> pts_to v.bytes s);
      x
    }
  }
}

fn node_len (n: node) (#sq: erased (Seq.seq tree))
    requires pts_to n.kids sq
    returns r: US.t
    ensures pts_to n.kids sq
{
  S.pts_to_len n.kids;
  S.len n.kids
}

fn main () returns r: US.t
    ensures emp
{
  let mut arr = [| 7uy; 3sz |];
  A.pts_to_len arr;
  let s = from_array arr 3sz;
  with sq. assert (pts_to s sq);
  let v = mk_view s;
  rewrite (pts_to s sq) as (pts_to v.bytes sq);
  let a = read_view v #sq;
  rewrite (pts_to v.bytes sq) as (pts_to s sq);
  let e = Tagged v;
  rewrite (pts_to s sq) as (match e with
                            | Whole b -> pts_to b sq
                            | Tagged w -> pts_to w.bytes sq);
  let b = read_either e #sq;
  rewrite (match e with
           | Whole b -> pts_to b sq
           | Tagged w -> pts_to w.bytes sq) as (pts_to s sq);
  to_array s;
  let mut karr = [| Leaf 1uy; 2sz |];
  A.pts_to_len karr;
  let ks = from_array karr 2sz;
  with kq. assert (pts_to ks kq);
  let n = { kids = ks };
  rewrite (pts_to ks kq) as (pts_to n.kids kq);
  let c = node_len n #kq;
  rewrite (pts_to n.kids kq) as (pts_to ks kq);
  to_array ks;
  if (a = 7uy && b = 7uy && c = 2sz) { 0sz } else { 1sz }
}

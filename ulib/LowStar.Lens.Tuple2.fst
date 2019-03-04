(*
   Copyright 2008-2019 Microsoft Research

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
module LowStar.Lens.Tuple2
open LowStar.Lens
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module BL = LowStar.Lens.Buffer
module Atomic = LowStar.Lens.Atomic

let composable (l1:hs_lens 'a 'b) (l2:hs_lens 'c 'd) =
    B.all_disjoint [Ghost.reveal l1.footprint;
                    Ghost.reveal l2.footprint] /\
    l1.snapshot == l2.snapshot

let tup2 (l1 : hs_lens 'a 'b) (l2 : hs_lens 'c 'd) =
  hs_lens ('a & 'c) ('b & 'd)

//abstract
let mk #a1 #b1 (l1 : hs_lens a1 b1)
       #a2 #b2 (l2 : hs_lens a2 b2{composable l1 l2})
  : tup2 l1 l2
  = let fp =
      Ghost.hide (
        B.loc_union_l [Ghost.reveal l1.footprint;
                       Ghost.reveal l2.footprint
                      ])
    in
    let inv (a, b) h : prop =
      l1.invariant a h /\
      l2.invariant b h
    in
    let x = l1.x, l2.x in
    let snap : imem (inv x) = l1.snapshot in
    let get : get_t (imem (inv x)) (b1 & b2) =
      fun h ->
        l1.l.get h,
        l2.l.get h
      in
    let put : put_t (imem (inv x)) (b1 & b2) =
      fun (v1, v2) h ->
         l2.l.put v2
        (l1.l.put v1 h)
    in
    let l : imem_lens (inv x) (b1 & b2) fp =
      {
        get = get;
        put = put;
        lens_laws = ()
      }
    in
    {
      footprint = fp;
      invariant = inv;
      x = x;
      l = l;
      snapshot = snap
    }

let op_fst #a #b #c #d #result #pre #post
      (l1:hs_lens a b)
      (l2:hs_lens c d{composable l1 l2})
      (op:with_state l1 result pre post)
  : LensST result (mk l1 l2)
    (requires fun (b0, d0) -> pre b0)
    (ensures fun (b0, d0) r (b1, d1) ->
      d0 == d1 /\
      post b0 r b1)
  = reveal_inv ();
    let s = FStar.HyperStack.ST.get () in
    op s

let op_snd #a #b #c #d #result #pre #post
      (l1:hs_lens a b)
      (l2:hs_lens c d{composable l1 l2})
      (op:with_state l2 result pre post)
  : LensST result (mk l1 l2)
    (requires fun (b0, d0) -> pre d0)
    (ensures fun (b0, d0) r (b1, d1) ->
      b0 == b1 /\
      post d0 r d1)
  = reveal_inv ();
    let s = FStar.HyperStack.ST.get () in
    op s

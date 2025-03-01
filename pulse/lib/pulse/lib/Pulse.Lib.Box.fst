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

module Pulse.Lib.Box

open Pulse.Lib.Core

module R = Pulse.Lib.Reference

#lang-pulse

noeq
type box a = | B : r:R.ref a -> box a

let pts_to b #p v = R.pts_to b.r #p v

let pts_to_timeless _ _ _ = ()

fn alloc (#a:Type0) (x:a)
  requires emp
  returns  b : box a
  ensures  pts_to b x
{
  let r = R.alloc x;
  rewrite R.pts_to r x as pts_to (B r) x;
  (B r);
}

fn op_Bang (#a:Type0) (b:box a) (#v:erased a) (#p:perm)
  requires pts_to b #p v
  returns  x : a
  ensures  pts_to b #p v ** pure (reveal v == x)
{
  unfold (pts_to b #p v);
  let x = R.(!b.r);
  fold (pts_to b #p v);
  x
}

fn op_Colon_Equals (#a:Type0) (b:box a) (x:a) (#v:erased a)
  requires pts_to b v
  ensures  pts_to b (hide x)
{
  unfold (pts_to b v);
  R.(b.r := x);
  fold (pts_to b (hide x));
}

#lang-fstar // 'rewrite' below is not the keyword!

let free b #v = R.free b.r #v

let share b = R.share b.r
let gather b = R.gather b.r
let pts_to_injective_eq b = R.pts_to_injective_eq b.r
let box_to_ref b = b.r
let to_ref_pts_to #a b #p #v =
  rewrite (pts_to b #p v) (R.pts_to b.r #p v) (slprop_equiv_refl _)
let to_box_pts_to #a b #p #v =
  rewrite (R.pts_to b.r #p v) (pts_to b #p v) (slprop_equiv_refl _)

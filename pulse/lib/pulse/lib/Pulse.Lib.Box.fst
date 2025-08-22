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

let null (#a:Type u#0) : box a = B R.null

let is_null #a (r : box a)
  : b:bool{b <==> r == null #a}
= R.is_null (B?.r r)

let pts_to b #p v = R.pts_to b.r #p v ** pure (R.is_full_ref b.r)

let pts_to_timeless _ _ _ = ()

(* This function is extracted primitively. The implementation
below is only a model, and uses the internal Ref.alloc. Hence
we disable the warning about using Ref.alloc. *)
#push-options "--warn_error -288"
fn alloc (#a:Type0) (x:a)
  requires emp
  returns  b : box a
  ensures  pts_to b x
{
  let r = R.alloc x;
  fold pts_to (B r) x;
  (B r);
}
#pop-options

fn op_Bang (#a:Type0) (b:box a) (#v:erased a) (#p:perm)
  preserves pts_to b #p v
  returns  x : a
  ensures rewrites_to x v
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

(* Same comment as for alloc. *)
#push-options "--warn_error -288"
fn free (#a:Type0) (b:box a) (#v:erased a)
  requires pts_to b v
{
  unfold pts_to b v;
  R.free b.r
}
#pop-options

ghost
fn share (#a:Type) (r:box a) (#v:erased a) (#p:perm)
  requires pts_to r #p v
  ensures pts_to r #(p /. 2.0R) v ** pts_to r #(p /. 2.0R) v
{
  unfold pts_to r #p v;
  R.share r.r;
  fold pts_to r #(p /. 2.0R) v;
  fold pts_to r #(p /. 2.0R) v;
}

[@@allow_ambiguous]
ghost
fn gather (#a:Type) (r:box a) (#x0 #x1:erased a) (#p0 #p1:perm)
  requires pts_to r #p0 x0 ** pts_to r #p1 x1
  ensures  pts_to r #(p0 +. p1) x0 ** pure (x0 == x1)
{
  unfold pts_to r #p0 x0;
  unfold pts_to r #p1 x1;
  R.gather r.r;
  fold pts_to r #(p0 +. p1) x0;
}

[@@allow_ambiguous]
ghost
fn pts_to_injective_eq (#a:_)
                        (#p #q:_)
                        (#v0 #v1:a)
                        (r:box a)
  requires pts_to r #p v0 ** pts_to r #q v1
  ensures  (pts_to r #p v0 ** pts_to r #q v1) ** pure (v0 == v1)
{
  unfold pts_to r #p v0;
  unfold pts_to r #q v1;
  R.pts_to_injective_eq r.r;
  fold pts_to r #p v0;
  fold pts_to r #q v1;
}

let box_to_ref b = b.r

#lang-fstar // 'rewrite' below is not the keyword!
let to_ref_pts_to #a b #p #v =
  rewrite _ _ (slprop_equiv_refl _)
let to_box_pts_to #a b #p #v =
  rewrite _ _ (slprop_equiv_refl _)
#lang-pulse

ghost
fn pts_to_not_null (#a:_) (#p:_) (r:box a) (#v:a)
  preserves r |-> Frac p v
  ensures  pure (not (is_null #a r))
{
  unfold (pts_to r #p v);
  R.pts_to_not_null (B?.r r);
  fold (pts_to r #p v);
}

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

module Pulse.Lib.Array.Core
#lang-pulse
open Pulse.Main
open FStar.Tactics.V2
open Pulse.Lib.Core
open PulseCore.FractionalPermission
open FStar.Ghost
module SZ = FStar.SizeT
module Seq = FStar.Seq
open FStar.PCM
module Frac = Pulse.Lib.PCM.Fraction
module PM = Pulse.Lib.PCM.Map
open Pulse.Lib.PCM.Array
module PA = Pulse.Lib.PCM.Array
open Pulse.Lib.PCMReference


/// An abstract type to represent a base array (whole allocation
/// unit), exposed for proof purposes only
[@@erasable]
noeq type base_t : Type0 = {
  base_len: base_len:nat { SZ.fits base_len };
  base_ref: base_ref:core_pcm_ref {
    base_ref == null_core_pcm_ref ==> base_len == 0
  };
}

noeq
type array' : Type0 = {
  base_len: base_len:Ghost.erased nat { SZ.fits base_len };
  base_ref: base_ref:core_pcm_ref {
    base_ref == null_core_pcm_ref ==> base_len == hide 0
  };
  offset: offset: nat { offset <= base_len };
  length: length:Ghost.erased nat {offset + length <= base_len };
}
let array elt = array'

let null_array' : array' = { base_len = 0; base_ref = null_core_pcm_ref; offset = 0; length = 0 }

let length (#elt: Type) (a: array elt) = a.length
let base_of #t (a: array t) : base_t = { base_len = a.base_len; base_ref = a.base_ref }
let offset_of #t (a: array t) : GTot nat = a.offset

let is_full_array (#elt: Type) (a: array elt) : Tot prop =
  length a == reveal a.base_len

let null #a : array a = null_array'
let is_null a = is_null_core_pcm_ref a.base_ref

let lptr_of #elt (a: array elt) : pcm_ref (PA.pcm elt a.base_len) =
  a.base_ref

[@@noextract_to "krml"]
let mk_carrier_f #elt (off: nat) (len: nat) (f: perm) (v: Seq.seq elt) (mask: nat -> bool) :
    index_t len -> Pulse.Lib.PCM.Fraction.fractional elt = fun i ->
  if off <= i && i < off + Seq.length v && mask (i - off) then
    Some (Seq.index v (i - off), f)
  else
    None

[@@noextract_to "krml"]
let mk_carrier #elt (off: nat) (len: nat) (f: perm) (v: Seq.seq elt) (mask: nat -> bool) : carrier elt len =
  Map.map_literal #(index_t len) #(Pulse.Lib.PCM.Fraction.fractional elt) (mk_carrier_f off len f v mask)

irreducible let pull_mask (f: nat -> prop) (len: nat) : Ghost (nat -> bool) (requires True)
    (ensures fun res -> forall i. res i <==> i >= len \/ f i) =
  let s = Seq.init_ghost len fun i -> IndefiniteDescription.strong_excluded_middle (f i) in
  fun i -> if i < len then Seq.index s i else true

let mk_carrier' #t (a: array t) (f: perm) (v: Seq.seq t) (mask: nat -> prop) : GTot (carrier t a.base_len) =
  mk_carrier a.offset a.base_len f v (pull_mask mask a.length)

let mask_nonempty (mask: nat -> prop) (len: nat) : prop =
  exists i. mask i /\ i < len

// workaround for https://github.com/FStarLang/pulse/issues/430
let squash' (t: Type u#a) = squash t
let intro_squash #t (x: t) : squash' t = ()

let pts_to_mask #t ([@@@mkey] a: array t) (#[full_default()] f: perm) (v: erased (Seq.seq t)) (mask: nat -> prop) : slprop =
  pcm_pts_to (lptr_of a) (mk_carrier' a f v mask) **
  pure (Seq.length v == reveal a.length /\ (mask_nonempty mask a.length ==> f <=. 1.0R) /\ squash' t)

let pts_to_mask_timeless _ _ _ _ = ()

ghost
fn pts_to_mask_props u#a (#t: Type u#a) (a:array t) (#p:perm) (#x:Seq.seq t) #mask
  preserves pts_to_mask a #p x mask
  ensures pure (length a == Seq.length x)
  ensures pure (mask_nonempty mask (length a) ==> p <=. 1.0R)
  ensures pure (~(is_null a))
  ensures pure (squash' t)
{
  unfold pts_to_mask a #p x mask;
  pts_to_not_null (lptr_of a) _;
  fold pts_to_mask a #p x mask;
}

ghost
fn pts_to_mask_len u#a (#t: Type u#a) (a:array t) (#p:perm) (#x:Seq.seq t) #mask
  preserves pts_to_mask a #p x mask
  ensures pure (length a == Seq.length x)
{
  pts_to_mask_props a;
}

ghost
fn pts_to_mask_perm_bound u#a (#t: Type u#a) (arr: array t) #p (#s:Seq.seq t) #mask
  preserves pts_to_mask arr #p s mask
  requires pure (exists (i: nat). i < Seq.length s /\ mask i)
  ensures pure (p <=. 1.0R)
{
  pts_to_mask_props arr;
}

ghost
fn pts_to_mask_not_null u#a (#a: Type u#a) #p (r:array a) (#v:Seq.seq a) #mask
  preserves pts_to_mask r #p v mask
  ensures pure (not (is_null r))
{
  pts_to_mask_props r;
}

ghost fn mask_vext u#a (#t: Type u#a) (arr: array t) #f #v v' #mask
  requires pts_to_mask arr #f v mask
  requires pure (Seq.length v' == Seq.length v /\
    (forall (i: nat). mask i /\ i < Seq.length v ==> Seq.index v i == Seq.index v' i))
  ensures pts_to_mask arr #f v' mask
{
  unfold pts_to_mask arr #f v mask;
  assert pure (mk_carrier' arr f v mask `Map.equal` mk_carrier' arr f v' mask);
  fold pts_to_mask arr #f v' mask;
}

ghost fn mask_mext u#a (#t: Type u#a) (arr: array t) #f #v #mask (mask': nat -> prop)
  requires pts_to_mask arr #f v mask
  requires pure (forall (i: nat). i < Seq.length v ==> (mask i <==> mask' i))
  ensures pts_to_mask arr #f v mask'
{
  unfold pts_to_mask arr #f v mask;
  assert pure (mk_carrier' arr f v mask `Map.equal` mk_carrier' arr f v mask');
  fold pts_to_mask arr #f v mask';
}

ghost fn mask_ext u#a (#t: Type u#a) (arr: array t) #f #v #mask v' (mask': nat -> prop)
  requires pts_to_mask arr #f v mask
  requires pure (forall (i: nat). i < Seq.length v ==> (mask i <==> mask' i))
  requires pure (Seq.length v' == Seq.length v /\
    (forall (i: nat). mask i /\ i < Seq.length v ==> Seq.index v i == Seq.index v' i))
  ensures pts_to_mask arr #f v' mask'
{
  mask_vext arr v';
  mask_mext arr mask';
}

[@@noextract_to "krml"]
fn mask_alloc u#a (#elt: Type u#a) {| small_type u#a |} (x: elt) (n: SZ.t)
  returns a: array elt
  ensures pts_to_mask a (Seq.create (SZ.v n) x) (fun _ -> True)
  ensures pure (length a == SZ.v n /\ is_full_array a)
{
  let v = mk_carrier 0 (SZ.v n) 1.0R (Seq.create (SZ.v n) x) (fun _ -> true);
  FStar.PCM.compatible_refl (PA.pcm elt (SZ.v n)) v;
  let b = alloc #_ #(PA.pcm elt (SZ.v n)) v;
  pts_to_not_null b _;
  let arr: array elt = { base_ref = b; base_len = SZ.v n; length = SZ.v n; offset = 0 };
  rewrite each b as lptr_of arr;
  assert pure (v `Map.equal` mk_carrier' arr 1.0R (Seq.create (SZ.v n) x) (fun _ -> l_True));
  intro_squash x;
  fold pts_to_mask arr (Seq.create (SZ.v n) x) (fun _ -> l_True);
  arr
}

[@@noextract_to "krml"]
fn mask_free u#a (#elt: Type u#a) (a: array elt) (#s: Ghost.erased (Seq.seq elt)) #mask
  requires pts_to_mask a s mask
  requires pure (forall i. mask i)
  requires pure (is_full_array a)
{
  drop_ (pts_to_mask a s mask);
}

let get_mask_idx (m: nat->prop) (l: nat) : GTot (i: nat { mask_nonempty m l ==> i < l /\ m i }) =
  if IndefiniteDescription.strong_excluded_middle (mask_nonempty m l) then
    IndefiniteDescription.indefinite_description_ghost nat fun i -> i < l /\ m i
  else
    0

ghost fn pcm_rw u#a (#t: Type u#a)
    (a1: array t) p1 s1 m1
    (a2: array t) p2 s2 m2
  requires pts_to_mask #t a1 #p1 s1 m1
  requires pure (
    a1.base_len == a2.base_len /\
    a1.base_ref == a2.base_ref /\
    reveal a2.length == Seq.length s2 /\
    mk_carrier' a1 p1 s1 m1 `Map.equal` mk_carrier' a2 p2 s2 m2
  )
  ensures pts_to_mask #t a2 #p2 s2 m2
{
  unfold pts_to_mask a1 #p1 s1 m1;
  rewrite each lptr_of a1 as lptr_of a2;
  let i = get_mask_idx m2 (length a2);
  assert pure (mask_nonempty m2 (length a2) ==>
    Map.sel (mk_carrier' a2 p2 s2 m2) (i + a2.offset) == Some (Seq.index s2 i, p2));
  fold pts_to_mask a2 #p2 s2 m2;
}

ghost fn pcm_share u#a (#t: Type u#a)
    (a: array t) p s m
    (a1: array t) p1 s1 m1
    (a2: array t) p2 s2 m2
  requires pts_to_mask a #p s m
  requires pure (Seq.length s1 == a1.length)
  requires pure (Seq.length s2 == a2.length)
  requires pure (
    a1.base_len == a.base_len /\ a2.base_len == a.base_len /\
    a1.base_ref == a.base_ref /\ a2.base_ref == a.base_ref /\
    composable (mk_carrier' a1 p1 s1 m1) (mk_carrier' a2 p2 s2 m2) /\
    compose (mk_carrier' a1 p1 s1 m1) (mk_carrier' a2 p2 s2 m2)
      `Map.equal` mk_carrier' a p s m
  )
  ensures pts_to_mask a1 #p1 s1 m1
  ensures pts_to_mask a2 #p2 s2 m2
{
  unfold pts_to_mask a #p s m;
  share (lptr_of a) (mk_carrier' a1 p1 s1 m1) (mk_carrier' a2 p2 s2 m2);
  rewrite
    pcm_pts_to (lptr_of a) (mk_carrier' a1 p1 s1 m1) as
    pcm_pts_to (lptr_of a1) (mk_carrier' a1 p1 s1 m1);
  rewrite
    pcm_pts_to (lptr_of a) (mk_carrier' a2 p2 s2 m2) as
    pcm_pts_to (lptr_of a2) (mk_carrier' a2 p2 s2 m2);
  let i1 = get_mask_idx m1 (length a1);
  let i2 = get_mask_idx m2 (length a2);
  assert pure (mask_nonempty m1 (length a1) ==>
    Some? (Map.sel (mk_carrier' a p s m) (i1 + a1.offset)));
  fold pts_to_mask a1 #p1 s1 m1;
  assert pure (mask_nonempty m2 (length a2) ==>
    Some? (Map.sel (mk_carrier' a p s m) (i2 + a2.offset)));
  fold pts_to_mask a2 #p2 s2 m2;
}

ghost fn pcm_gather u#a (#t: Type u#a)
    (a: array t) p s m
    (a1: array t) p1 s1 m1
    (a2: array t) p2 s2 m2
  requires pure (Seq.length s == a.length)
  requires pure (
    a1.base_len == a.base_len /\ a2.base_len == a.base_len /\
    a1.base_ref == a.base_ref /\ a2.base_ref == a.base_ref /\
    (composable (mk_carrier' a1 p1 s1 m1) (mk_carrier' a2 p2 s2 m2) ==>
    compose (mk_carrier' a1 p1 s1 m1) (mk_carrier' a2 p2 s2 m2)
      `Map.equal` mk_carrier' a p s m)
  )
  requires pts_to_mask a1 #p1 s1 m1
  requires pts_to_mask a2 #p2 s2 m2
  ensures pts_to_mask a #p s m
  ensures pure (
    a1.base_len == a.base_len /\ a2.base_len == a.base_len /\
    a1.base_ref == a.base_ref /\ a2.base_ref == a.base_ref /\
    composable (mk_carrier' a1 p1 s1 m1) (mk_carrier' a2 p2 s2 m2) /\
    compose (mk_carrier' a1 p1 s1 m1) (mk_carrier' a2 p2 s2 m2)
      `Map.equal` mk_carrier' a p s m
  )
{
  unfold pts_to_mask a1 #p1 s1 m1;
  unfold pts_to_mask a2 #p2 s2 m2;
  rewrite
    pcm_pts_to (lptr_of a1) (mk_carrier' a1 p1 s1 m1) as
    pcm_pts_to (lptr_of a) (mk_carrier' a1 p1 s1 m1);
  rewrite
    pcm_pts_to (lptr_of a2) (mk_carrier' a2 p2 s2 m2) as
    pcm_pts_to (lptr_of a) (mk_carrier' a2 p2 s2 m2);
  gather (lptr_of a) (mk_carrier' a1 p1 s1 m1) (mk_carrier' a2 p2 s2 m2);
  let i = get_mask_idx m (length a);
  assert pure (mask_nonempty m a.length ==>
    Map.sel (mk_carrier' a p s m) (i + a.offset) == Some (Seq.index s i, p));
  fold pts_to_mask a #p s m;
}

ghost
fn mask_share u#a (#a: Type u#a) (arr:array a) (#s: Seq.seq a) #p #mask
  requires pts_to_mask arr #p s mask
  ensures pts_to_mask arr #(p /. 2.0R) s mask
  ensures pts_to_mask arr #(p /. 2.0R) s mask
{
  pts_to_mask_props arr;
  pcm_share
    arr p s mask
    arr (p /. 2.0R) s mask
    arr (p /. 2.0R) s mask;
}

[@@allow_ambiguous]
ghost fn mask_gather u#a (#t: Type u#a) (arr: array t) #p1 #p2 #s1 #s2 #mask1 #mask2
  requires pts_to_mask arr #p1 s1 mask1
  requires pts_to_mask arr #p2 s2 mask2
  requires pure (forall i. mask1 i <==> mask2 i)
  ensures exists* (v: Seq.seq t). pts_to_mask arr #(p1 +. p2) v mask1 **
    pure ((Seq.length v == Seq.length s1 /\ Seq.length v == Seq.length s2) /\
      (forall (i: nat). i < Seq.length v /\ mask1 i ==> Seq.index v i == Seq.index s1 i /\ Seq.index v i == Seq.index s2 i))
{
  mask_mext arr #p2 #s2 mask1;
  pts_to_mask_props arr #p1 #s1 #mask1;
  pts_to_mask_props arr #p2 #s2 #mask1;
  pcm_gather
    arr (p1 +. p2) s1 mask1
    arr p1 s1 mask1
    arr p2 s2 mask1;
  assert pure (forall (i: nat). (i < Seq.length s1 /\ mask1 i) ==>
    Map.sel (mk_carrier' arr p1 s1 mask1) (i + arr.offset) == Some (Seq.index s1 i, p1));
}

ghost fn split_mask u#a (#t: Type u#a) (arr: array t) #f #v #mask (pred: nat -> prop)
  requires pts_to_mask arr #f v mask
  ensures pts_to_mask arr #f v (mask_isect mask pred)
  ensures pts_to_mask arr #f v (mask_diff mask pred)
{
  pts_to_mask_props arr;
  pcm_share
    arr f v mask
    arr f v (mask_isect mask pred)
    arr f v (mask_diff mask pred);
}

let mix #t (v1: Seq.seq t) (v2: Seq.seq t { Seq.length v1 == Seq.length v2 }) (mask: nat -> prop) :
    GTot (res: Seq.seq t { Seq.length res == Seq.length v1 /\
      (forall (i: nat). i < Seq.length res ==>
        (mask i ==> Seq.index res i == Seq.index v1 i) /\
        (~(mask i) ==> Seq.index res i == Seq.index v2 i)) }) =
  Seq.init_ghost (Seq.length v1) fun i ->
    if IndefiniteDescription.strong_excluded_middle (mask i) then Seq.index v1 i else Seq.index v2 i

[@@allow_ambiguous]
ghost fn join_mask u#a (#t: Type u#a) (arr: array t) #f #v1 #v2 #mask1 #mask2
  requires pts_to_mask arr #f v1 mask1
  requires pts_to_mask arr #f v2 mask2
  requires pure (forall i. ~(mask1 i /\ mask2 i))
  ensures exists* (v: Seq.seq t).
    pts_to_mask arr #f v (fun i -> mask1 i \/ mask2 i) **
    pure (Seq.length v == Seq.length v1 /\ Seq.length v == Seq.length v2 /\
      (forall (i: nat). i < Seq.length v ==>
        (mask1 i ==> Seq.index v i == Seq.index v1 i) /\
        (mask2 i ==> Seq.index v i == Seq.index v2 i)))
{
  pts_to_mask_props arr #f #v1 #mask1;
  pts_to_mask_props arr #f #v2 #mask2;
  let v = mix v1 v2 mask1;
  with mask. assert pure (mask == (fun i -> mask1 i \/ mask2 i));
  pcm_gather
    arr f v mask
    arr f v1 mask1
    arr f v2 mask2;
}

[@@allow_ambiguous]
ghost fn join_mask' u#a (#t: Type u#a) (arr: array t) #f (#v: erased (Seq.seq t)) #mask1 #mask2
  requires pts_to_mask arr #f v mask1
  requires pts_to_mask arr #f v mask2
  requires pure (forall i. ~(mask1 i /\ mask2 i))
  ensures pts_to_mask arr #f v (fun i -> mask1 i \/ mask2 i)
{
  join_mask arr #f #v #v #mask1 #mask2;
  mask_vext arr v;
}

[@@allow_ambiguous]
ghost
fn pts_to_mask_injective_eq u#a (#a: Type u#a) #p0 #p1 #s0 #s1 #mask0 #mask1 (arr:array a)
  preserves pts_to_mask arr #p0 s0 mask0
  preserves pts_to_mask arr #p1 s1 mask1
  ensures pure (Seq.length s0 == Seq.length s1 /\
    (forall (i: nat). i < Seq.length s0 /\ mask0 i /\ mask1 i ==>
      Seq.index s0 i == Seq.index s1 i))
{
  unfold pts_to_mask arr #p0 s0 mask0;
  unfold pts_to_mask arr #p1 s1 mask1;
  gather (lptr_of arr) (mk_carrier' arr p0 s0 mask0) (mk_carrier' arr p1 s1 mask1);
  share (lptr_of arr) (mk_carrier' arr p0 s0 mask0) (mk_carrier' arr p1 s1 mask1);
  assert pure (forall (i: nat). i < Seq.length s0 /\ mask0 i ==>
    Map.sel (mk_carrier' arr p0 s0 mask0) (i + arr.offset) == Some (Seq.index s0 i, p0));
  fold pts_to_mask arr #p0 s0 mask0;
  fold pts_to_mask arr #p1 s1 mask1;
}

[@@noextract_to "krml"]
fn mask_read u#a (#t: Type u#a) (a: array t) (i: SZ.t) #p (#s: erased (Seq.seq t) { SZ.v i < Seq.length s }) #mask
  preserves pts_to_mask a #p s mask
  requires pure (mask (SZ.v i))
  returns res: t
  ensures pure (res == Seq.index s (SZ.v i))
{
  unfold pts_to_mask a #p s mask;
  with w. assert pcm_pts_to (lptr_of a) w;
  let v = read (lptr_of a) w (fun _ -> w);
  fold pts_to_mask a #p s mask;
  fst (Some?.v (FStar.Map.sel v (a.offset + SZ.v i)));
}

[@@noextract_to "krml"]
fn mask_write u#a (#t: Type u#a) (a: array t) (i: SZ.t) (v: t) (#s: erased (Seq.seq t) { SZ.v i < Seq.length s }) #mask
  requires pts_to_mask a s mask
  requires pure (mask (SZ.v i))
  ensures pts_to_mask a (Seq.upd s (SZ.v i) v) mask
{
  unfold pts_to_mask a s mask;
  with w. assert (pcm_pts_to (lptr_of a) w);
  write (lptr_of a) w _
      (PM.lift_frame_preserving_upd
        _ _
        (Frac.mk_frame_preserving_upd
          (Seq.index s (SZ.v i))
          v
        )
        _ (a.offset + SZ.v i));
  assert pure (
    Map.upd (mk_carrier' a 1.0R s mask) (a.offset + SZ.v i) (Some (v, 1.0R))
    `Map.equal`
    mk_carrier' a 1.0R (Seq.upd s (SZ.v i) v) mask
  );
  fold pts_to_mask a (Seq.upd s (SZ.v i) v) mask;
}

[@@noextract_to "krml"]
let sub_impl #t (arr: array t) (i: nat) (j: erased nat { i <= j /\ j <= length arr }) : array t =
  { arr with offset = arr.offset + i; length = j - i }

let gsub #t (arr: array t) (i: nat) (j: nat { i <= j /\ j <= length arr }) : GTot (array t) =
  sub_impl arr i j

let length_gsub #t arr i j = ()
let offset_of_gsub #t arr i j = ()
let base_of_gsub #t arr i j = ()

ghost fn gsub_intro u#a (#t: Type u#a) (arr: array t) #f #mask (i j: nat) (#v: erased (Seq.seq t) { i <= j /\ j <= Seq.length v })
  requires pts_to_mask arr #f v mask
  requires pure (forall (k: nat). mask k /\ k < Seq.length v ==> i <= k /\ k < j)
  returns _: squash (length arr == Seq.length v)
  ensures pts_to_mask (gsub arr i j) #f (Seq.slice v i j) (fun k -> mask (k + i))
{
  pts_to_mask_props arr;
  pcm_rw
    arr f v mask
    (gsub arr i j) f (Seq.slice v i j) (fun k -> mask (k + i));
  ()
}

let elim_squash (t: Type u#a { squash' t }) : GTot t =
  let h : squash (squash' t) = () in
  let h : squash t = IndefiniteDescription.elim_squash h in
  IndefiniteDescription.elim_squash h

ghost fn gsub_elim u#a (#t: Type u#a) (arr: array t) #f (#mask: nat->prop) (i j: nat)
    (#v: erased (Seq.seq t) { i <= j /\ j <= length arr })
  requires pts_to_mask (gsub arr i j) #f v mask
  returns _: squash (j - i == Seq.length v)
  ensures exists* (v': Seq.seq t).
    pts_to_mask arr #f v' (fun k -> i <= k /\ k < j /\ mask (k - i)) **
    pure (Seq.length v' == length arr /\ (forall (k:nat). k < j - i ==> Seq.index v k == Seq.index v' (k + i)))
{
  pts_to_mask_props (gsub arr i j);
  let dummy = elim_squash t;
  let v' = Seq.init_ghost (length arr) (fun k ->
    if i <= k && k < j then Seq.index v (k - i) else dummy);
  pcm_rw
    (gsub arr i j) f v mask
    arr f v' (fun k -> i <= k /\ k < j /\ mask (k - i));
  ()
}

[@@noextract_to "krml"]
unobservable
fn sub u#a (#t: Type u#a) (arr: array t) #f #mask (i: SZ.t) (j: erased nat)
    (#v: erased (Seq.seq t) { SZ.v i <= j /\ j <= Seq.length (reveal v) })
  requires pts_to_mask arr #f v mask
  returns sub: (sub: array t { length arr == Seq.length (reveal v) })
  ensures rewrites_to sub (gsub arr (SZ.v i) j)
  ensures pts_to_mask sub #f (Seq.slice v (SZ.v i) j) (fun k -> mask (k + SZ.v i))
  ensures pts_to_mask arr #f v (fun k -> mask k /\ ~(SZ.v i <= k /\ k < j))
{
  let pred = (fun k -> SZ.v i <= k /\ k < j);
  pts_to_mask_props arr;
  split_mask arr pred;
  gsub_intro arr #f #(mask_isect mask pred) (SZ.v i) j;
  mask_mext (gsub arr (SZ.v i) j) (fun k -> mask (k + SZ.v i));
  rewrite each gsub arr (SZ.v i) j as sub_impl arr (SZ.v i) j;
  sub_impl arr (SZ.v i) j
}

[@@allow_ambiguous]
ghost fn return_sub u#a (#t: Type u#a) (arr: array t) #f (#v #vsub: erased (Seq.seq t)) #mask #masksub (#i: nat) (#j: nat { i <= j /\ j <= length arr })
  requires pts_to_mask arr #f v mask
  requires pts_to_mask (gsub arr i j) #f vsub masksub
  requires pure (forall (k: nat). i <= k /\ k < j ==> ~(mask k))
  ensures exists* v'. pts_to_mask arr #f v' (fun k -> mask k \/ (i <= k /\ k < j /\ masksub (k - i)))
    ** pure (Seq.length v == Seq.length v' /\ i + Seq.length vsub == j /\ j <= Seq.length v /\
      (forall (k: nat). k < Seq.length v' ==>
      Seq.index v' k == (if i <= k && k < j then Seq.index vsub (k - i) else Seq.index v k)))
{
  gsub_elim arr i j;
  join_mask arr;
  let v' = Seq.init_ghost (Seq.length v) (fun k -> 
    if i <= k && k < j then Seq.index vsub (k - i) else Seq.index v k);
  mask_ext arr v' (fun k -> mask k \/ (i <= k /\ k < j /\ masksub (k - i)));
}
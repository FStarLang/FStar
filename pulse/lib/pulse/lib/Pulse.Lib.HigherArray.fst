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

module Pulse.Lib.HigherArray
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


/// An abstract type to represent a base array (whole allocation
/// unit), exposed for proof purposes only
[@@erasable]
let base_t
: Type0
= Ghost.erased (SZ.t & core_pcm_ref)

let base_len (b: base_t) : GTot nat = SZ.v (fst b)

/// An abstract type to represent a C pointer, as a base and an offset
/// into its base
let l_pcm_ref (elt:Type u#a) (base_len:SZ.t) =
  r:pcm_ref (PA.pcm elt (SZ.v base_len)){ 
      r =!= null_core_pcm_ref \/
      base_len = 0sz
  }


noeq
type ptr : Type0 = {
  base_len: Ghost.erased SZ.t;
  base: (base:core_pcm_ref { base == null_core_pcm_ref ==> SZ.v base_len == 0});
  offset: (offset: nat { offset <= SZ.v base_len });
}


let null_ptr
: ptr
= { base_len = 0sz; base = null_core_pcm_ref ; offset = 0 }


let is_null_ptr (p:ptr)
: Pure bool
  (requires True)
  (ensures (fun res -> res == true <==> p == null_ptr))
= is_null_core_pcm_ref p.base

let base (p: ptr)
: Tot base_t
= ( Ghost.reveal p.base_len, p.base )

let offset (p: ptr)
: Ghost nat (requires True) (ensures (fun offset -> offset <= base_len (base p)))
= p.offset

let ptr_base_offset_inj (p1 p2: ptr) : Lemma
  (requires (
    base p1 == base p2 /\
    offset p1 == offset p2
  ))
  (ensures (
    p1 == p2
  ))
= ()

let base_len_null_ptr : squash  (base_len (base (null_ptr)) == 0)
= ()

noeq
type array'
: Type0
= { p: ptr;
    length: (l:Ghost.erased nat {offset p + l <= base_len (base p)})
  }
let array ([@@@strictly_positive] elt: Type u#1) : Type0 = array'
let length (#elt: Type) (a: array elt) = a.length

let ptr_of
  (#elt: Type)
  (a: array elt)
: Tot (ptr)
= a.p

let is_full_array (#elt: Type) (a: array elt) : Tot prop =
  length a == base_len (base (ptr_of a))

let null (#a: Type u#1) : array a
= { p = null_ptr; length =Ghost.hide 0 }

let length_fits #elt a = ()

let valid_perm
  (len: nat)
  (offset: nat)
  (slice_len: nat)
  (p: perm)
: prop
= let open FStar.Real in
  ((offset + slice_len <= len /\ slice_len > 0) ==> (p <=. one))

let l_pcm_ref' (elt:Type u#a) (base_len:SZ.t) =
  r:pcm_ref (PA.pcm elt (SZ.v base_len))

let lptr_of (#elt:Type u#1) (a:array elt)
  : Tot (l_pcm_ref elt ( (ptr_of a).base_len))
  = (ptr_of a).base

let pts_to (#elt: Type u#1) (a: array elt) (#p: perm) (s: Seq.seq elt) : Tot slprop =
  pcm_pts_to
    (lptr_of a)
    (mk_carrier (SZ.v (ptr_of a).base_len) (ptr_of a).offset s p) **
  pure (
    valid_perm (SZ.v (ptr_of a).base_len) (ptr_of a).offset (Seq.length s) p /\
    Seq.length s == length a
  )

let pts_to_is_slprop2 _ _ _ = ()

let mk_array
    (#elt: Type u#1)
    (base_len: SZ.t)
    (base:l_pcm_ref elt base_len)
    (offset:nat { offset <= SZ.v base_len})
: array elt
= { p = { base_len; base; offset} ; length = Ghost.hide (SZ.v base_len - offset) }


ghost
fn fold_pts_to
    (#elt: Type u#1)
    (base_len: SZ.t)
    (base:l_pcm_ref elt base_len)
    (offset:nat { offset <= SZ.v base_len})
    (#p: perm { p <=. 1.0R})
    (s: Seq.seq elt { Seq.length s == SZ.v base_len - offset})
requires
  pcm_pts_to base (mk_carrier (SZ.v base_len) offset s p)
ensures
  pts_to (mk_array base_len base offset) #p s
{
  let a = (mk_array base_len base offset);
  rewrite (pcm_pts_to base (mk_carrier (SZ.v base_len) offset s p))
      as pcm_pts_to (lptr_of a)
            (mk_carrier (SZ.v (ptr_of a).base_len) 
                        (ptr_of a).offset
                        s p);
  fold (pts_to a #p s);
  rewrite (pts_to a #p s)
        as (pts_to (mk_array base_len base offset) #p s);
}




ghost
fn pts_to_len'
  (#elt: Type u#1)
  (a:array elt)
  (#p:perm)
  (#x:Seq.seq elt)
requires pts_to a #p x
ensures pts_to a #p x ** pure (length a == Seq.length x)
{
  unfold pts_to a #p x;
  fold pts_to a #p x;
}

let pts_to_len = pts_to_len'



fn alloc' 
    (#elt: Type u#1)
    (x: elt)
    (n: SZ.t)
requires emp
returns a:array elt
ensures 
  pts_to a (Seq.create (SZ.v n) x) **
  pure (length a == SZ.v n /\ is_full_array a)
{
  let v = (mk_carrier (SZ.v n) 0 (Seq.create (SZ.v n) x) 1.0R);
  FStar.PCM.compatible_refl (PA.pcm elt (SZ.v n)) v;
  let b = Pulse.Lib.Core.alloc #_ #(PA.pcm elt (SZ.v n)) v;
  pts_to_not_null b _;
  fold_pts_to n b 0 #1.0R (Seq.create (SZ.v n) x);
  mk_array n b 0;
}

let alloc = alloc'


fn read
    (#t: Type)
    (a: array t)
    (i: SZ.t)
    (#p: perm)
    (#s: Ghost.erased (Seq.seq t){SZ.v i < Seq.length s})
requires pts_to a #p s
returns res:t
ensures 
    pts_to a #p s **
    pure (res == Seq.index s (SZ.v i))
{
  unfold pts_to a #p s;
  with w. assert (pcm_pts_to (lptr_of a) w);
  let v = Pulse.Lib.Core.read (lptr_of a) w (fun _ -> w);
  fold (pts_to a #p s);
  fst (Some?.v (FStar.Map.sel v ((ptr_of a).offset + SZ.v i)));
}

let op_Array_Access = read

let mk_carrier_upd
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s: Seq.seq elt)
  (i: nat)
  (v: elt)
  (_: squash (
    offset + Seq.length s <= len /\
    i < Seq.length s
  ))
: Lemma
  (ensures (
    let o = mk_carrier len offset s 1.0R in
    let o' = mk_carrier len offset (Seq.upd s i v) 1.0R in
    o' `Map.equal` Map.upd o (offset + i) (Some (v, 1.0R))
  ))
= ()


fn write
    (#t: Type)
    (a: array t)
    (i: SZ.t)
    (v: t)
    (#s: Ghost.erased (Seq.seq t) {SZ.v i < Seq.length s})
requires pts_to a s
ensures pts_to a (Seq.upd s (SZ.v i) v)
{
  unfold pts_to a #1.0R s;
  with w. assert (pcm_pts_to (lptr_of a) w);
  mk_carrier_upd (SZ.v (ptr_of a).base_len) ((ptr_of a).offset) s (SZ.v i) v ();
  Pulse.Lib.Core.write (lptr_of a) w _
      (PM.lift_frame_preserving_upd
        _ _
        (Frac.mk_frame_preserving_upd
          (Seq.index s (SZ.v i))
          v
        )
        _ ((ptr_of a).offset + SZ.v i));
  fold (pts_to a #1.0R (Seq.upd s (SZ.v i) v));
}

let op_Array_Assignment = write

(*
let frame_preserving_upd_one (#elt:Type) (n:erased nat) (s:erased (Seq.seq elt) { Seq.length s == reveal n })
 : FStar.PCM.frame_preserving_upd (PA.pcm elt n)
      (mk_carrier n 0 s 1.0R)
      (PA.one #elt #n)
= fun _ -> admit(); (PA.one #elt #n) 
 *)


fn free'
    (#elt: Type)
    (a: array elt)
    (#s: Ghost.erased (Seq.seq elt))
requires
  pts_to a s **
  pure (is_full_array a)
ensures 
  emp
{
  unfold pts_to a #1.0R s;
  with w. assert (pcm_pts_to (lptr_of a) w);
  // Pulse.Lib.Core.write (ptr_of a).base w (PA.one #elt #(length a)) (frame_preserving_upd_one #elt (length a) s);
  drop_ (pcm_pts_to (lptr_of a) _)
}

let free = free'

let valid_sum_perm
  (len: nat)
  (offset: nat)
  (slice_len: nat)
  (p1 p2: perm)
: Tot prop
= let open FStar.Real in
  valid_perm len offset slice_len (p1 +. p2)


ghost
fn mk_carrier_share
  (#elt: Type u#1)
  (len: nat)
  (offset: nat)
  (s: Seq.seq elt)
  (p1 p2: perm)
  (_:squash (valid_sum_perm len offset (Seq.length s) p1 p2))
requires emp
ensures 
(
  // let c1 = (mk_carrier len offset s p1) in
  pure (
    composable (mk_carrier len offset s p1)
               (mk_carrier len offset s p2) /\
    mk_carrier len offset s (p1 +. p2) 
      `Map.equal` 
    ((mk_carrier len offset s p1) `compose` (mk_carrier len offset s p2))
  )
)
  
{
  ()
}



ghost
fn share'
  (#elt:Type)
  (arr:array elt)
  (#s:Ghost.erased (Seq.seq elt))
  (#p:perm)
requires pts_to arr #p s
ensures pts_to arr #(p /. 2.0R) s ** pts_to arr #(p /. 2.0R) s
{
  unfold pts_to arr #p s;
  with w. assert (pcm_pts_to (lptr_of arr) w);
  mk_carrier_share (SZ.v (ptr_of arr).base_len)
       (ptr_of arr).offset
       s
       (p /. 2.0R) 
       (p /. 2.0R) ();
  Pulse.Lib.Core.share (lptr_of arr)
    (mk_carrier (SZ.v (ptr_of arr).base_len) (ptr_of arr).offset s (p /. 2.0R))
    (mk_carrier (SZ.v (ptr_of arr).base_len) (ptr_of arr).offset s (p /. 2.0R));
  fold pts_to arr #(p /. 2.0R) s;
  fold pts_to arr #(p /. 2.0R) s;
}

let share = share'

let mk_carrier_gather
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s1 s2: Seq.seq elt)
  (p1 p2: perm)
  (_:squash (
    let c1 = mk_carrier len offset s1 p1 in
    let c2 = mk_carrier len offset s2 p2 in
    composable c1 c2 /\
    Seq.length s1 == Seq.length s2 /\
    offset + Seq.length s1 <= len
  ))
: squash (
    let c1 = mk_carrier len offset s1 p1 in
    let c2 = mk_carrier len offset s2 p2 in
      composable c1 c2 /\
      mk_carrier len offset s1 (p1 +. p2) == (c1 `compose` c2) /\
      mk_carrier len offset s2 (p1 +. p2) == (c1 `compose` c2) /\
      s1 == s2
  )
=
  let c1 = mk_carrier len offset s1 p1 in
  let c2 = mk_carrier len offset s2 p2 in
  assert (composable c1 c2);
  assert (mk_carrier len offset s1 (p1 +. p2) `Map.equal` (c1 `compose` c2));
  assert (mk_carrier len offset s2 (p1 +. p2) `Map.equal` (c1 `compose` c2));
  mk_carrier_inj len offset s1 s2 (p1 +. p2) (p1 +. p2)


let mk_carrier_valid_sum_perm
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s: Seq.seq elt)
  (p1 p2: perm)
: squash
  (let c1 = mk_carrier len offset s p1 in
   let c2 = mk_carrier len offset s p2 in
   composable c1 c2 <==> valid_sum_perm len offset (Seq.length s) p1 p2)
= let c1 = mk_carrier len offset s p1 in
  let c2 = mk_carrier len offset s p2 in
  if Seq.length s > 0 && offset + Seq.length s <= len
  then
    let open FStar.Real in
    assert (Frac.composable (Map.sel c1 offset) (Map.sel c2 offset) <==> valid_perm len offset (Seq.length s) (p1 +. p2))
  else ()


ghost
fn of_squash (#p:prop) (s:squash p)
requires emp
ensures pure p
{
  ()
}



ghost
fn gather'
  (#a:Type)
  (arr:array a)
  (#s0 #s1:Ghost.erased (Seq.seq a))
  (#p0 #p1:perm)
requires pts_to arr #p0 s0 ** pts_to arr #p1 s1
ensures pts_to arr #(p0 +. p1) s0 ** pure (s0 == s1)
{
  unfold pts_to arr #p0 s0;
  with w0. assert (pcm_pts_to (lptr_of arr) w0);
  unfold pts_to arr #p1 s1;
  with w1. assert (pcm_pts_to (lptr_of arr) w0 ** pcm_pts_to (lptr_of arr) w1);
  Pulse.Lib.Core.gather (lptr_of arr) w0 w1;
  of_squash (mk_carrier_gather (SZ.v (ptr_of arr).base_len) ((ptr_of arr).offset) s0 s1 p0 p1 ());
  of_squash (mk_carrier_valid_sum_perm (SZ.v (ptr_of arr).base_len) ((ptr_of arr).offset) s0 p0 p1);
  fold pts_to arr #(p0 +. p1) s0;
}

let gather = gather'

let ptr_shift
  (p: ptr)
  (off: nat {offset p + off <= base_len (base p)})
: ptr
= {
    base_len = p.base_len;
    base = p.base;
    offset = p.offset + off;
  }

let split_l'
    (#elt: Type)
    (a: array elt)
    (i: erased nat {i <= length a})
: array elt
= { p = ptr_of a; length=i }

irreducible
let split_l
  (#elt: Type)
  (a: array elt)
  (i: erased nat {i <= length a})
: x:array elt { x == split_l' a i }
= split_l' a i

let split_r'
  (#elt: Type)
  (a: array elt)
  (i: nat {i <= length a})
: array elt
= { p= ptr_shift (ptr_of a) i; length=Ghost.hide (length a - i) }

irreducible
let split_r
  (#elt: Type)
  (a: array elt)
  (i: nat {i <= length a})
: x:array elt { x == split_r' a i }
= split_r' a i

let array_slice
  (#elt: Type)
  (a: array elt)
  (i:nat) (j: nat {i <= j /\ j <= length a})
: GTot (array elt)
= split_l (split_r a i) (j - i)

let in_bounds (i j:nat) (s:array 'a) = squash (i <= j /\ j <= length s)

ghost
fn elim_in_bounds (#elt:Type) (#i #j:nat) (s:array elt) (p:in_bounds i j s)
requires emp
ensures pure (i <= j /\ j <= length s)
{
  ()
}


let token (x:'a) = emp

let pts_to_range
  (#a:Type)
  ([@@@equate_strict] x:array a)
  (i j : nat)
  (#[exact (`1.0R)] p:perm)
  (s : Seq.seq a)
: slprop
= exists* (q:in_bounds i j x). pts_to (array_slice x i j) #p s ** token q

let pts_to_range_is_slprop2 (#a:Type) (x:array a) (i j : nat) (p:perm) (s:Seq.seq a)
  : Lemma (is_slprop2 (pts_to_range x i j #p s))
          [SMTPat (is_slprop2 (pts_to_range x i j #p s))]
  =
    let aux (q:in_bounds i j x) : Lemma (is_slprop2 (pts_to (array_slice x i j) #p s ** token q))
    =
      ()
    in
    Classical.forall_intro aux;
    assert_norm (pts_to_range x i j #p s == (exists* (q:in_bounds i j x). pts_to (array_slice x i j) #p s ** token q));
    slprop2_exists (fun (q: in_bounds i j x) -> pts_to (array_slice x i j) #p s ** token q)


ghost
fn pts_to_range_prop'
  (#elt: Type)
  (a: array elt)
  (#i #j: nat)
  (#p: perm)
  (#s: Seq.seq elt)
requires pts_to_range a i j #p s
ensures pts_to_range a i j #p s ** pure (
      (i <= j /\ j <= length a /\ Seq.length s == j - i)
    )
{
  unfold pts_to_range a i j #p s;
  with q. assert (token #(in_bounds i j a) q);
  elim_in_bounds a q;
  pts_to_len (array_slice a i j);
  fold pts_to_range a i j #p s;
}

let pts_to_range_prop = pts_to_range_prop'


ghost
fn pts_to_range_intro'
  (#elt: Type)
  (a: array elt)
  (p: perm)
  (s: Seq.seq elt)
requires pts_to a #p s
ensures pts_to_range a 0 (length a) #p s
{
  rewrite each a as (array_slice a 0 (length a));
  let q : in_bounds 0 (length a) a = ();
  fold (token #(in_bounds 0 (length a) a) q);
  fold (pts_to_range a 0 (length a) #p s);
}

let pts_to_range_intro = pts_to_range_intro'



ghost
fn pts_to_range_elim'
  (#elt: Type)
  (a: array elt)
  (p: perm)
  (s: Seq.seq elt)
requires pts_to_range a 0 (length a) #p s
ensures pts_to a #p s
{
  unfold (pts_to_range a 0 (length a) #p s);
  unfold (token #(in_bounds 0 (length a) a) _);
  rewrite each (array_slice a 0 (length a)) as a;
}

let pts_to_range_elim = pts_to_range_elim'

let mk_carrier_split
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s: Seq.seq elt)
  (p: perm)
  (i: nat)
  (_:squash (
    offset + Seq.length s <= len /\
    i <= Seq.length s
  ))
: squash (
    let c1 = mk_carrier len offset (Seq.slice s 0 i) p in
    let c2 = mk_carrier len (offset + i) (Seq.slice s i (Seq.length s)) p in
      composable c1 c2 /\
      mk_carrier len offset s p `Map.equal` (c1 `compose` c2)
  )
= ()


ghost
fn use_squash (#p:prop) (s:squash p)
requires emp
ensures pure p
{
  ()
}



ghost
fn ghost_split
  (#elt: Type)
  (#x: Seq.seq elt)
  (#p: perm)
  (a: array elt)
  (i: nat {i <= length a})
requires pts_to a #p x
returns _: squash (i <= length a /\ i <= Seq.length x)
ensures
    pts_to (split_r a i) #p (Seq.slice x i (Seq.length x)) **
    pts_to (split_l a i) #p (Seq.slice x 0 i) **
    pure (x `Seq.equal` Seq.append (Seq.slice x 0 i) (Seq.slice x i (Seq.length x)))
{
  unfold (pts_to a #p x);
  use_squash (mk_carrier_split (SZ.v (ptr_of a).base_len) (ptr_of a).offset x p i ());
  let xl = Seq.slice x 0 i;
  let xr = Seq.slice x i (Seq.length x);
  let vl = mk_carrier (SZ.v (ptr_of a).base_len) ((ptr_of a).offset) xl p;
  let vr = mk_carrier (SZ.v (ptr_of a).base_len) ((ptr_of a).offset + i) xr p;
  Pulse.Lib.Core.share (lptr_of a) vl vr;
  rewrite pcm_pts_to (lptr_of a) vl
      as  pcm_pts_to (lptr_of (split_l a i)) vl;
  rewrite pcm_pts_to (lptr_of a) vr
      as  pcm_pts_to (lptr_of (split_r a i)) vr;
  fold (pts_to (split_l a i) #p xl);
  fold (pts_to (split_r a i) #p xr);
}


let slprop_equiv_refl_eq (v0 v1:slprop) (_:squash (v0 == v1)) : slprop_equiv v0 v1 = 
  slprop_equiv_refl v0

let equiv () : FStar.Tactics.Tac unit =
  let open FStar.Tactics in
  mapply (`slprop_equiv_refl_eq);
  smt()


ghost
fn split_l_slice #elt
     (a : array elt)
     (i m j: nat)
     (#s:Seq.seq elt)
     (#p:perm)
     (_:squash (i <= m /\ m <= j /\ j <= length a))
requires pts_to (split_l (array_slice a i j) (m - i)) #p s
ensures  pts_to (array_slice a i m) #p s
{
  rewrite each (split_l (array_slice a i j) (m - i))
             as (array_slice a i m);
}



ghost
fn split_r_slice #elt
     (a:array elt)
     (i m j: nat)
     (#s:Seq.seq elt)
     (#p:perm)
     (_:squash (i <= m /\ m <= j /\ j <= length a))
requires pts_to (split_r (array_slice a i j) (m - i)) #p s
ensures pts_to (array_slice a m j) #p s
{
  rewrite each (split_r (array_slice a i j) (m - i)) as (array_slice a m j);
}



ghost
fn pts_to_range_split'
  (#elt: Type)
  (a: array elt)
  (i m j: nat)
  (#p: perm)
  (#s: Seq.seq elt)
requires
  pts_to_range a i j #p s **
  pure (i <= m /\ m <= j)
ensures
  exists* s1 s2.
    pts_to_range a i m #p s1 **
    pts_to_range a m j #p s2 **
    pure (
      i <= m /\ m <= j /\ j <= length a /\
      eq2 #int (Seq.length s) (j - i) /\
      s1 == Seq.slice s 0 (m - i) /\
      s2 == Seq.slice s (m - i) (Seq.length s) /\
      s == Seq.append s1 s2
    )
{
  pts_to_range_prop a;
  unfold pts_to_range a i j #p s;
  unfold (token #(in_bounds i j a) _);
  ghost_split (array_slice a i j) (m - i);
  split_r_slice a i m j #(Seq.slice s (m - i) (Seq.length s)) ();
  split_l_slice a i m j ();
  let q1 : in_bounds i m a = ();
  let q2 : in_bounds m j a = ();
  fold (token #(in_bounds i m a) q1);
  fold (token #(in_bounds m j a) q2);
  fold (pts_to_range a i m #p (Seq.slice s 0 (m - i)));
  fold (pts_to_range a m j #p (Seq.slice s (m - i) (Seq.length s)));
  assert pure (s `Seq.equal` Seq.append (Seq.slice s 0 (m - i)) (Seq.slice s (m - i) (Seq.length s)));
}

let pts_to_range_split = pts_to_range_split'


let mk_carrier_merge
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s1 s2: Seq.seq elt)
  (p: perm)
  (_:squash (
    offset + Seq.length s1 + Seq.length s2 <= len
  ))
: squash (
    let c1 = mk_carrier len offset s1 p in
    let c2 = mk_carrier len (offset + Seq.length s1) s2 p in
      composable c1 c2 /\
      mk_carrier len offset (s1 `Seq.append` s2) p `Map.equal` (c1 `compose` c2)
  )
= ()

let adjacent (#elt: Type) (a1 a2: array elt) : Tot prop =
  base (ptr_of a1) == base (ptr_of a2) /\
  offset (ptr_of a1) + (length a1) == offset (ptr_of a2)

let merge' (#elt: Type) (a1: array elt) (a2:array elt { adjacent a1 a2 })
= { p = ptr_of a1; length=Ghost.hide (length a1 + length a2) }

irreducible
let merge #elt (a1:array elt) (a2:array elt{ adjacent a1 a2})
: i:array elt{ i == merge' a1 a2 } 
= merge' a1 a2


ghost
fn ghost_join
  (#elt: Type)
  (#x1 #x2: Seq.seq elt)
  (#p: perm)
  (a1 a2: array elt)
  (h: squash (adjacent a1 a2))
requires pts_to a1 #p x1 ** pts_to a2 #p x2
ensures pts_to (merge a1 a2) #p (x1 `Seq.append` x2)
{
  unfold pts_to a1 #p x1;
  unfold pts_to a2 #p x2;
  use_squash (mk_carrier_merge (SZ.v (ptr_of a1).base_len) ((ptr_of a1).offset) x1 x2 p ());
  with w. rewrite 
          pcm_pts_to (lptr_of a2) w
      as  pcm_pts_to (lptr_of a1) (mk_carrier (SZ.v (ptr_of a1).base_len) ((ptr_of a1).offset + Seq.length x1) x2 p);
  Pulse.Lib.Core.gather (lptr_of a1)
    (mk_carrier (SZ.v (ptr_of a1).base_len) ((ptr_of a1).offset) x1 (p))
    (mk_carrier (SZ.v (ptr_of a1).base_len) ((ptr_of a1).offset + Seq.length x1) x2 (p));
  with w. rewrite
          pcm_pts_to (lptr_of a1) w
      as  pcm_pts_to 
              (lptr_of (merge a1 a2))
              (mk_carrier (SZ.v (ptr_of (merge a1 a2)).base_len)
                          ((ptr_of (merge a1 a2)).offset) (x1 `Seq.append` x2) (p));
  fold (pts_to (merge a1 a2) #p (Seq.append x1 x2));
}



ghost
fn pts_to_range_intro_ij
  (#elt: Type)
  (a: array elt)
  (p: perm)
  (s: Seq.seq elt)
  (i j: nat)
  (_:squash (i <= j /\ j <= length a))
requires pts_to (array_slice a i j) #p s
ensures pts_to_range a i j #p s
{
  let q : in_bounds i j a = ();
  fold (token #(in_bounds i j a) q);
  fold (pts_to_range a i j #p s);
}



ghost
fn pts_to_range_join'
  (#elt: Type)
  (a: array elt)
  (i m j: nat)
  (#p: perm)
  (#s1 #s2: Seq.seq elt)
requires
  pts_to_range a i m #p s1 ** pts_to_range a m j #p s2
ensures pts_to_range a i j #p (s1 `Seq.append` s2)
{
  pts_to_range_prop a #i #m;
  pts_to_range_prop a #m #j;
  unfold pts_to_range a i m #p s1;
  unfold pts_to_range a m j #p s2;
  ghost_join (array_slice a i m) (array_slice a m j) ();
  rewrite each (merge (array_slice a i m) (array_slice a m j))
            as (array_slice a i j);
  pts_to_range_intro_ij a _ _ i j ();
  unfold (token #(in_bounds i m a) _);
  unfold (token #(in_bounds m j a) _);
}

let pts_to_range_join = pts_to_range_join'

irreducible
let array_slice_impl
  (#elt: Type)
  (a: array elt)
  (i: SZ.t)
  (j: Ghost.erased nat)
  (sq: squash (SZ.v i <= j /\ j <= length a))
: x:array elt { x == array_slice a (SZ.v i) j }
= split_l (split_r a (SZ.v i)) (Ghost.hide (j - SZ.v i))


fn pts_to_range_index'
  (#t: Type)
  (a: array t)
  (i: SZ.t)
  (#l: Ghost.erased nat{l <= SZ.v i})
  (#r: Ghost.erased nat{SZ.v i < r})
  (#s: Ghost.erased (Seq.seq t))
  (#p: perm)
requires pts_to_range a l r #p s
returns res:t
ensures
  pts_to_range a l r #p s **
  pure (eq2 #int (Seq.length s) (r - l) /\
        res == Seq.index s (SZ.v i - l))
{
  pts_to_range_split a l (SZ.v i) r;
  with s1 s2. _;
  unfold pts_to_range a (SZ.v i) r #p s2;
  unfold (token #(in_bounds (SZ.v i) r a) _);
  let a' = array_slice_impl a i r ();
  rewrite each (array_slice a (SZ.v i) r) as a';
  let res = read a' 0sz;
  rewrite each a' as (array_slice a (SZ.v i) r);
  pts_to_range_intro_ij a _ _ (SZ.v i) r ();
  pts_to_range_join a l (SZ.v i) r;
  res
}

let pts_to_range_index = pts_to_range_index'


fn pts_to_range_upd'
  (#t: Type)
  (a: array t)
  (i: SZ.t)
  (v: t)
  (#l: Ghost.erased nat{l <= SZ.v i})
  (#r: Ghost.erased nat{SZ.v i < r})
  (#s0: Ghost.erased (Seq.seq t))
requires pts_to_range a l r #1.0R s0
ensures
  exists* s.
    pts_to_range a l r s **
    pure (
        eq2 #int (Seq.length s0) (r - l) /\
        s == Seq.upd s0 (SZ.v i - l) v
    )
{
  pts_to_range_split a l (SZ.v i) r;
  with s1 s2. _;
  unfold pts_to_range a (SZ.v i) r #1.0R s2;
  unfold (token #(in_bounds (SZ.v i) r a) _);
  let a' = array_slice_impl a i r ();
  rewrite each (array_slice a (SZ.v i) r) as a';
  write a' 0sz v;
  rewrite each a' as (array_slice a (SZ.v i) r);
  pts_to_range_intro_ij a _ _ (SZ.v i) r ();
  pts_to_range_join a l (SZ.v i) r;
  with w. assert (pts_to_range a l r w);
  assert pure (w `Seq.equal` Seq.upd s0 (SZ.v i - l) v);
}

let pts_to_range_upd = pts_to_range_upd'

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

module Pulse.Lib.Reference
#lang-pulse
open Pulse.Lib.Core
open Pulse.Main
module H = Pulse.Lib.HigherReference
friend Pulse.Lib.Array.Core
module U = Pulse.Lib.Raise
inline_for_extraction
let ref a = H.ref (U.raise_t a)

inline_for_extraction
let null (#a:Type u#0) : ref a = H.null

inline_for_extraction
let is_null #a (r : ref a)
  : b:bool{b <==> r == null #a}
= H.is_null r

let pts_to
    (#a:Type u#0)
    (r:ref a)
    (#p:perm)
    (v:a)
  = H.pts_to r #p (U.raise_val v)

let pts_to_timeless r p x = H.pts_to_timeless r p (U.raise_val x)

let is_full_ref r = H.is_full_ref r

inline_for_extraction
fn alloc (#a:Type u#0) (v:a)
  returns r:ref a
  ensures pts_to r v
  ensures  pure (is_full_ref r)
{
  let r = H.alloc (U.raise_val v);
  fold (pts_to r #1.0R v);
  r
}



inline_for_extraction
fn read
  (#a:Type)
  (r:ref a)
  (#n:erased a)
  (#p:perm)
  preserves pts_to r #p n
  returns x:a
  ensures rewrites_to x n
{
  unfold (pts_to r #p n);
  let k = H.( !r );
  fold (pts_to r #p n);
  U.downgrade_val k
}

inline_for_extraction
let op_Bang = read

inline_for_extraction
fn write
  (#a:Type)
  (r:ref a)
  (x:a)
  (#n:erased a)
  requires pts_to r #1.0R n
  ensures pts_to r #1.0R x
{
  unfold (pts_to r #1.0R n);
  H.(r := (U.raise_val x));
  fold (pts_to r #1.0R x)
}

inline_for_extraction
let op_Colon_Equals = write

inline_for_extraction
fn free #a (r:ref a) (#n:erased a)
  requires pts_to r #1.0R n
  requires pure (is_full_ref r)
{
  unfold (pts_to r #1.0R n);
  H.free r;
}



ghost
fn share (#a:Type) (r:ref a) (#v:erased a) (#p:perm)
  requires pts_to r #p v
  ensures pts_to r #(p /. 2.0R) v ** pts_to r #(p /. 2.0R) v
{
  unfold pts_to r #p v;
  H.share r;
  fold pts_to r #(p /. 2.0R) v;
  fold pts_to r #(p /. 2.0R) v
}



ghost
fn raise_inj (a:Type u#0) (x0 x1:a)
  requires pure (U.raise_val u#0 u#1 x0 == U.raise_val u#0 u#1 x1)
  ensures pure (x0 == x1)
{
  assert pure (U.downgrade_val (U.raise_val u#0 u#1 x0) == x0);
  assert pure (U.downgrade_val (U.raise_val u#0 u#1 x1) == x1);
}



ghost
fn gather (#a:Type) (r:ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  requires pts_to r #p0 x0 ** pts_to r #p1 x1
  ensures pts_to r #(p0 +. p1) x0 ** pure (x0 == x1)
{
  unfold pts_to r #p0 x0;
  unfold pts_to r #p1 x1;
  H.gather r;
  fold (pts_to r #(p1 +. p0) x0);
  raise_inj a x0 x1;
}



fn
raise_exists (#a:Type u#0) (frame:slprop) (p: U.raise_t u#0 u#1 a -> slprop)
  requires frame ** (exists* (x:a). p (U.raise_val x))
  ensures frame ** (exists* (x:U.raise_t a). p x)
{
  ()
}


let with_local
    (#a:Type0)
    (init:a)
    (#pre:slprop)
    (#ret_t:Type)
    (#post:ret_t -> slprop)
    (body:(r:ref a) -> stt ret_t (pre ** pts_to r init)
                                 (fun v -> post v ** op_exists_Star (pts_to r #1.0R)))
: stt ret_t pre post
= let body (r:H.ref (U.raise_t a))
    : stt ret_t (pre ** H.pts_to r #1.0R (U.raise_val init))
                (fun v -> post v ** (exists* (x:U.raise_t a). H.pts_to r #1.0R x)) 
    = let m
        : stt ret_t (pre ** H.pts_to r #1.0R (U.raise_val init))
                    (fun v -> post v ** (exists* (x:a). H.pts_to r #1.0R (U.raise_val x)))
        = body r
      in
      let m0 (v:ret_t)
        : stt ret_t 
            (post v ** (exists* (x:a). H.pts_to r #1.0R (U.raise_val x)))
            (fun v -> post v ** (exists* (x:U.raise_t a). H.pts_to r #1.0R x))
        = bind_stt (raise_exists (post v) (H.pts_to r #1.0R))
                   (fun _ -> return_stt_noeq v (fun v -> post v ** (exists* (x:U.raise_t a). H.pts_to r #1.0R x)))
      in
      bind_stt m m0
  in
  H.with_local (U.raise_val init) body


ghost
fn pts_to_injective_eq
  (#a:Type0)
  (#p #q:perm)
  (#v0 #v1:a)
  (r:ref a)
requires
  pts_to r #p v0 ** pts_to r #q v1
ensures
  pts_to r #p v0 ** pts_to r #q v1 ** pure (v0 == v1)
{
  unfold pts_to r #p v0;
  unfold pts_to r #q v1;
  H.pts_to_injective_eq r;
  fold pts_to r #p v0;
  fold pts_to r #q v1;
  raise_inj _ v0 v1;
}



ghost
fn pts_to_perm_bound (#a:_) (#p:_) (r:ref a) (#v:a)
  requires pts_to r #p v
  ensures pts_to r #p v ** pure (p <=. 1.0R)
{
  unfold pts_to r #p v;
  H.pts_to_perm_bound r;
  fold pts_to r #p v;
}


ghost
fn pts_to_not_null (#a:_) (#p:_) (r:ref a) (#v:a)
  preserves r |-> Frac p v
  ensures  pure (not (is_null #a r))
{
  unfold pts_to r #p v;
  let res = H.pts_to_not_null r;
  fold pts_to r #p v;
  res
}

fn replace (#a:Type0) (r:ref a) (x:a) (#v:erased a)
  requires pts_to r v
  returns y:a
  ensures pts_to r x ** pure (y == reveal v)
{
  let y = !r;
  r := x;
  y
}

let to_array_ghost r = H.to_array_ghost r

inline_for_extraction
unobservable
fn to_array #a (r: ref a) #p (#v: erased a)
  requires r |-> Frac p v
  returns arr: array a
  ensures rewrites_to arr (to_array_ghost r)
  ensures arr |-> Frac p (seq![reveal v])
  ensures pure (length arr == 1)
{
  unfold pts_to r #p v;
  let res = H.to_array r;
  assert pure (raise_seq seq![reveal v] `Seq.equal` seq![U.raise_val (reveal v)]);
  fold Pulse.Lib.Array.Core.pts_to res #p seq![reveal v];
  res;
}

ghost
fn return_to_array #a (r: ref a) #p (#v: Seq.seq a)
  requires to_array_ghost r |-> Frac p v
  requires pure (length (to_array_ghost r) == 1)
  returns _: squash (Seq.length v == 1)
  ensures r |-> Frac p (Seq.index v 0)
{
  unfold Pulse.Lib.Array.Core.pts_to (to_array_ghost r) #p v;
  H.return_to_array r #p #(raise_seq v);
  fold pts_to r #p (Seq.index v 0);
}

let array_at_ghost arr i = H.array_at_ghost arr i

inline_for_extraction
unobservable
fn array_at #a (arr: array a) (i: SizeT.t) #p (#v: erased (Seq.seq a) { SizeT.v i < length arr /\ length arr == Seq.length v }) #mask
  requires pts_to_mask arr #p v mask
  requires pure (mask (SizeT.v i))
  returns r: ref a
  ensures rewrites_to r (array_at_ghost arr (SizeT.v i))
  ensures r |-> Frac p (Seq.index v (SizeT.v i))
  ensures pts_to_mask arr #p v (fun k -> mask k /\ k <> SizeT.v i)
{
  unfold pts_to_mask arr #p v mask;
  let res = H.array_at arr i;
  fold pts_to_mask arr #p v (fun k -> mask k /\ k <> SizeT.v i);
  fold pts_to (H.array_at_ghost arr (SizeT.v i)) #p (Seq.Base.index v (SizeT.v i));
  res
}

ghost
fn return_array_at #a (arr: array a) (i: nat) (#p: perm) (#v: a) (#v': Seq.seq a { i < length arr /\ length arr == Seq.length v' }) (#mask: nat->prop)
  requires array_at_ghost arr i |-> Frac p v
  requires pts_to_mask arr #p v' mask
  requires pure (~(mask i))
  ensures pts_to_mask arr #p (Seq.upd v' i v) (fun k -> mask k \/ k == i)
{
  unfold pts_to (array_at_ghost arr i) #p v;
  H.return_array_at arr i;
  assert pure (raise_seq (Seq.Base.upd v' i v) `Seq.equal` Seq.upd (raise_seq v') i (U.raise_val v));
  fold pts_to_mask arr #p (Seq.upd v' i v) (fun k -> mask k \/ k == i);
}
(*
   Copyright 2020 Microsoft Research

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

module Steel.ST.Reference
open FStar.Ghost
open Steel.ST.Util
open Steel.ST.Coercions
module R = Steel.Reference

let ref (a:Type0)
  : Type0
  = R.ref a

let null (#a:Type0)
  : ref a
  = R.null #a

let is_null (#a:Type0) (r:ref a)
  : b:bool{b <==> r == null}
  = R.is_null r

let pts_to (#a:Type0)
           (r:ref a)
           ([@@@smt_fallback] p:perm)
           ([@@@smt_fallback] v:a)
  : vprop
  = R.pts_to r p v

let pts_to_injective_eq
      (#a: Type)
      (#opened:inames)
      (#p0 #p1:perm)
      (#v0 #v1:a)
      (r: ref a)
  : STGhost unit opened
      (pts_to r p0 v0 `star` pts_to r p1 v1)
      (fun _ -> pts_to r p0 v0 `star` pts_to r p1 v0)
      (requires True)
      (ensures fun _ -> v0 == v1)
  = coerce_ghost
    (fun _ -> R.pts_to_injective_eq #a #opened #p0 #p1 #(hide v0) #(hide v1) r)

let pts_to_not_null #a #opened #p #v r
  = extract_fact #opened (pts_to r p v) (r =!= null) (R.pts_to_not_null r p v);
    ()

let alloc (#a:Type) (x:a)
  : ST (ref a)
      emp
      (fun r -> pts_to r full_perm x)
      (requires True)
      (ensures fun r -> not (is_null r))
  = let r = coerce_steel (fun _ -> R.alloc_pt x) in
    r

let read (#a:Type)
         (#p:perm)
         (#v:erased a)
         (r:ref a)
  : ST a
      (pts_to r p v)
      (fun _ -> pts_to r p v)
      (requires True)
      (ensures fun x -> x == Ghost.reveal v)
  = let u = coerce_steel (fun _ -> R.read_pt r) in
    return u

let write (#a:Type0)
          (#v:erased a)
          (r:ref a)
          (x:a)
  : STT unit
      (pts_to r full_perm v)
      (fun _ -> pts_to r full_perm x)
  = coerce_steel (fun _ -> R.write_pt r x);
    return ()

let free (#a:Type0)
         (#v:erased a)
         (r:ref a)
  : STT unit
        (pts_to r full_perm v)
        (fun _ -> emp)
  = coerce_steel(fun _ -> R.free_pt r);
    return ()


let share (#a:Type0)
          (#uses:_)
          (#p:perm)
          (#v:erased a)
          (r:ref a)
  : STGhostT unit uses
      (pts_to r p v)
      (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)
  = coerce_ghost (fun _ -> R.share_pt r)

let gather (#a:Type0)
           (#uses:_)
           (#p0 p1:perm)
           (#v0 #v1:erased a)
           (r:ref a)
  : STGhost unit uses
      (pts_to r p0 v0 `star` pts_to r p1 v1)
      (fun _ -> pts_to r (sum_perm p0 p1) v0)
      (requires True)
      (ensures fun _ -> v0 == v1)
  = coerce_ghost (fun _ -> R.gather_pt #a #uses #p0 #p1 #v0 #v1 r)

let atomic_read_u32 r =
  let u = coerce_atomic (fun _ -> R.atomic_read_pt_u32 r) in
  return u

let atomic_write_u32 r x =
  coerce_atomic (fun _ -> R.atomic_write_pt_u32 r x);
  return ()

let cas_u32 #uses v r v_old v_new =
  coerce_atomic (fun _ -> R.cas_pt_u32 #uses r v v_old v_new)

let ptrp r p = R.ptrp r p
let ptrp_sel r p = R.ptrp_sel r p

module SA = Steel.Effect.Atomic

let vptrp_intro'
  (#inames: _)
  (#a: Type) (r: ref a) (p: perm) (v: a)
: SA.SteelGhostT unit inames
    (pts_to r p v)
    (fun _ -> vptrp r p `vrefine` C.equals v)
=
  R.intro_vptr r p v;
  SA.change_slprop
    (R.vptrp r p)
    (vptrp r p)
    v
    v
    (fun _ -> ());
  SA.intro_vrefine (vptrp r p) (C.equals v)

let vptrp_intro r p v =
  coerce_ghost (fun _ -> vptrp_intro' r p v)

let vptrp_elim'
  (#inames: _)
  (#a: Type) (r: ref a) (p: perm) (v: a)
: SA.SteelGhostT unit inames
    (vptrp r p `vrefine` C.equals v)
    (fun _ -> pts_to r p v)
=
  SA.elim_vrefine (vptrp r p) (C.equals v);
  SA.change_slprop
    (vptrp r p)
    (R.vptrp r p)
    v
    v
    (fun _ -> ());
  let v' = R.elim_vptr r p in
  SA.change_slprop_rel
    (R.pts_to r p v')
    (R.pts_to r p v)
    (fun _ _ -> True)
    (fun _ -> ())

let vptrp_elim r p v =
  coerce_ghost (fun _ -> vptrp_elim' r p v)

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

module Steel.ST.MonotonicReference
open FStar.Ghost
open Steel.ST.Util
open Steel.ST.Coercions
module Preorder = FStar.Preorder
module MR = Steel.MonotonicReference

let ref (a:Type u#0) (p:Preorder.preorder a)
  : Type u#0
  = MR.ref a p

let pts_to (#a:Type)
           (#p:Preorder.preorder a)
           (r:ref a p)
           ([@@@smt_fallback]f:perm)
           ([@@@smt_fallback]v:a)
   : vprop
   = MR.pts_to #a #p r f v

let alloc (#a:Type) (p:Preorder.preorder a) (v:a)
  : STT (ref a p) emp (fun r -> pts_to r full_perm v)
  = let x = coerce_steel (fun _ -> MR.alloc p v) in
    return x

let write (#a:Type) (#p:Preorder.preorder a) (#v:erased a)
          (r:ref a p) (x:a)
  : ST unit
      (pts_to r full_perm v)
      (fun v -> pts_to r full_perm x)
      (requires p v x)
      (ensures fun _ -> True)
  = coerce_steel (fun _ -> MR.write r x)

let witnessed (#a:Type u#0)
              (#p:Preorder.preorder a)
              (r:ref a p)
              (fact:property a)
  : prop
  = MR.witnessed r fact

let witness' (#inames: _)
            (#a:Type)
            (#q:perm)
            (#p:Preorder.preorder a)
            (r:ref a p)
            (fact:stable_property p)
            (v:erased a)
            (pf:squash (fact v))
            (_:unit)
  : Steel.Effect.Atomic.SteelGhost unit inames
      (pts_to r q v)
      (fun _ -> pts_to r q v)
      (requires fun _ -> True)
      (ensures fun _ _ _ -> witnessed r fact)
  = MR.witness #inames #a #q #p r fact v pf

let witness (#inames: _)
            (#a:Type)
            (#q:perm)
            (#p:Preorder.preorder a)
            (r:ref a p)
            (fact:stable_property p)
            (v:erased a)
            (pf:squash (fact v))
  : STGhost unit inames
      (pts_to r q v)
      (fun _ -> pts_to r q v)
      (requires True)
      (ensures fun _ -> witnessed r fact)
  = coerce_ghost (witness' r fact v pf); ()

let recall (#inames: _)
           (#a:Type u#0)
           (#q:perm)
           (#p:Preorder.preorder a)
           (fact:property a)
           (r:ref a p)
           (v:erased a)
  : STGhost unit inames
      (pts_to r q v)
      (fun _ -> pts_to r q v)
      (requires witnessed r fact)
      (ensures fun _ -> fact v)
  = coerce_ghost (fun _ -> MR.recall #inames #a #q #p fact r v)

let share (#inames:_)
          (#a:Type)
          (#p:Preorder.preorder a)
          (r:ref a p)
          (f:perm)
          (v:Ghost.erased a)
  : STGhostT unit inames
    (pts_to r f v)
    (fun _ -> pts_to r (half_perm f) v `star` pts_to r (half_perm f) v)
  = coerce_ghost (fun _ -> MR.share r f v)

let gather (#inames:_)
           (#a:Type)
           (#p:Preorder.preorder a)
           (r:ref a p)
           (f g:perm)
           (v:Ghost.erased a)
  : STGhostT unit inames
    (pts_to r f v `star` pts_to r g v)
    (fun _ -> pts_to r (sum_perm f g) v)
  = coerce_ghost (fun _ -> MR.gather #inames #a #p r f g v)

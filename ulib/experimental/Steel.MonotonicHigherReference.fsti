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
   limitations under the License.o
*)

module Steel.MonotonicHigherReference

open FStar.PCM
open FStar.Ghost
open Steel.FractionalPermission

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect

module Preorder = FStar.Preorder

val ref (a:Type u#1) (p:Preorder.preorder a)
  : Type u#0

val pts_to_sl (#a:Type) (#p:Preorder.preorder a) (r:ref a p) (f:perm) (v:erased a)
  : slprop u#1

[@@ __steel_reduce__]
unfold let pts_to (#a:Type) (#p:Preorder.preorder a) (r:ref a p) (f:perm) (v:erased a) : vprop =
  to_vprop (pts_to_sl r f v)

val alloc (#a:Type) (p:Preorder.preorder a) (v:a)
  : SteelT (ref a p) emp (fun r -> pts_to r full_perm v)

val read_refine (#a:Type) (#q:perm) (#p:Preorder.preorder a) (#frame:a -> vprop)
                (r:ref a p)
  : SteelT a (h_exists (fun (v:a) -> pts_to r q v `star` frame v))
             (fun v -> pts_to r q v `star` frame v)

val write (#a:Type) (#p:Preorder.preorder a) (#v:erased a)
          (r:ref a p) (x:a)
  : Steel unit (pts_to r full_perm v)
               (fun v -> pts_to r full_perm x)
               (requires fun _ -> p v x /\ True)
               (ensures fun _ _ _ -> True)

let property (a:Type)
  = a -> prop

val witnessed (#a:Type u#1) (#p:Preorder.preorder a) (r:ref a p) (fact:property a)
  : prop

let stable_property (#a:Type) (p:Preorder.preorder a)
  = fact:property a { Preorder.stable fact p }

val witness (#a:Type) (#q:perm) (#p:Preorder.preorder a) (r:ref a p)
            (fact:stable_property p)
            (v:erased a)
            (_:squash (fact v))
  : Steel unit (pts_to r q v)
               (fun _ -> pts_to r q v)
               (requires fun _ -> True)
               (ensures fun _ _ _ -> witnessed r fact)

val recall (#a:Type u#1) (#q:perm) (#p:Preorder.preorder a)
           (fact:property a)
           (r:ref a p) (v:erased a)
  : Steel unit (pts_to r q v)
               (fun _ -> pts_to r q v)
               (requires fun _ -> witnessed r fact)
               (ensures fun _ _ _ -> fact v)

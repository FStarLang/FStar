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

module Steel.PCM.HigherReference
open Steel.PCM.Effect
open Steel.PCM.Effect.Atomic
open Steel.PCM.Memory
open Steel.PCM.FractionalPermission
open FStar.Ghost

val ref (a:Type u#1) : Type u#0

val pts_to (#a:Type u#1) (r:ref a) (p:perm) (v:erased a) : slprop u#1

val alloc (#a:Type) (x:a)
  : SteelT (ref a) emp (fun r -> pts_to r full_perm x)

val read (#a:Type) (#p:perm) (#v:erased a) (r:ref a)
  : SteelT a (pts_to r p v) (fun x -> pts_to r p x)

val read_refine (#a:Type) (#p:perm) (q:a -> slprop) (r:ref a)
  : SteelT a (h_exists (fun (v:a) -> pts_to r p v `star` q v))
             (fun v -> pts_to r p v `star` q v)

val write (#a:Type) (#v:erased a) (r:ref a) (x:a)
  : SteelT unit (pts_to r full_perm v) (fun _ -> pts_to r full_perm x)

val free (#a:Type) (#v:erased a) (r:ref a)
  : SteelT unit (pts_to r full_perm v) (fun _ -> emp)

val share_atomic (#a:Type) (#uses:_) (#p:perm) (#v:erased a) (r:ref a)
  : SteelAtomic unit uses unobservable
    (pts_to r p v)
    (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)

val share (#a:Type) (#p:perm) (#v:erased a) (r:ref a)
  : SteelT unit
    (pts_to r p v)
    (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)

val gather_atomic (#a:Type) (#uses:_) (#p0:perm) (#p1:perm) (#v0 #v1:erased a) (r:ref a)
  : SteelAtomic (_:unit{v0==v1}) uses unobservable
    (pts_to r p0 v0 `star` pts_to r p1 v1)
    (fun _ -> pts_to r (sum_perm p0 p1) v0)

val gather (#a:Type) (#p0:perm) (#p1:perm) (#v0 #v1:erased a) (r:ref a)
  : SteelT (_:unit{v0==v1})
    (pts_to r p0 v0 `star` pts_to r p1 v1)
    (fun _ -> pts_to r (sum_perm p0 p1) v0)

val ghost_read_refine (#a:Type) (#uses:inames) (#p:perm) (r:ref a) (q:a -> slprop)
  : SteelAtomic a uses unobservable
    (h_exists (fun (v:a) -> pts_to r p v `star` q v))
    (fun v -> pts_to r p v `star` q v)


// val pure (p:prop) : hprop

// val lem_star_pure (p : hprop) (f: prop)
//   : Lemma (requires f)
//           (ensures (p `equiv` (p `star` pure f)))

// val lem_interp_star_pure (p: hprop) (f: prop) (m: mem)
//   : Lemma (requires (interp (p `star` pure f)) m)
//           (ensures f)

// let property (a:Type) = a -> prop

// val witnessed (#a:Type u#1) (#p:Preorder.preorder a) (r:reference a p)
//               (fact:property a) : prop

// let stable_property (#a:Type) (p:Preorder.preorder a) = fact:property a { Preorder.stable fact p }

// val witness (#a:Type) (#q:perm) (#p:Preorder.preorder a) (r:reference a p)
//             (fact:stable_property p)
//             (v:(Ghost.erased a))
//             (_:squash (fact v))
//   : SteelT unit (pts_to_ref r q v)
//                 (fun _ -> pts_to_ref r q v `star` pure (witnessed r fact))

// val recall (#a:Type u#1) (#q:perm) (#p:Preorder.preorder a) (#fact:property a)
//            (r:reference a p) (v:(Ghost.erased a))
//   : SteelT unit (pts_to_ref r q v `star` pure (witnessed r fact))
//                 (fun _ -> pts_to_ref r q v `star` pure (fact v))

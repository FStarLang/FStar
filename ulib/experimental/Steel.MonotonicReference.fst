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

module Steel.MonotonicReference

open FStar.PCM
open FStar.Ghost
open Steel.FractionalPermission

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect

module Preorder = FStar.Preorder
module MHR = Steel.MonotonicHigherReference
module U = FStar.Universe

let raise_preorder (#a:Type0) (p:Preorder.preorder a)
  : Preorder.preorder (U.raise_t a)
  = fun (x0 x1:U.raise_t a) ->
       p (U.downgrade_val x0) (U.downgrade_val x1)

let ref a p = MHR.ref (FStar.Universe.raise_t a) (raise_preorder p)

/// The standard points to separation logic predicate
let pts_to_sl (#a:Type) (#p:Preorder.preorder a)
              (r:ref a p)
              (f:perm)
              (v:a)
    = MHR.pts_to_sl r f (hide (U.raise_val v))

/// Allocates a reference with value [x]. We have full permission on the newly
/// allocated reference.
let alloc (#a:Type) (p:Preorder.preorder a) (v:a)
  : SteelT (ref a p) emp (fun r -> pts_to r full_perm v)
  = let r = MHR.alloc (raise_preorder p) (U.raise_val v) in
    rewrite_slprop
      (MHR.pts_to r full_perm (hide (U.raise_val v)))
      (pts_to r full_perm v)
      (fun _ -> ());
    return r


/// Writes value [x] in the reference [r], as long as we have full ownership of [r]
let write (#a:Type) (#p:Preorder.preorder a) (#v:erased a)
          (r:ref a p) (x:a)
  : Steel unit (pts_to r full_perm v)
               (fun v -> pts_to r full_perm x)
               (requires fun _ -> p v x /\ True)
               (ensures fun _ _ _ -> True)
  = MHR.write r (U.raise_val x);
    rewrite_slprop
      (MHR.pts_to _ _ _)
      (pts_to r full_perm x)
      (fun _ -> ())

let lift_property (#a:Type u#0) (p:property a)
  : MHR.property (U.raise_t a)
  = fun x -> p (U.downgrade_val x)

let witnessed (#a:Type u#0)
              (#p:Preorder.preorder a)
              (r:ref a p)
              (fact:property a)
  = MHR.witnessed r (lift_property fact)

/// If [fact] is a stable property for the reference preorder [p], and if
/// it holds for the current value [v] of the reference, then we can witness it
let witness (#inames: _)
           (#a:Type)
           (#q:perm)
           (#p:Preorder.preorder a)
           (r:erased (ref a p))
           (fact:stable_property p)
           (v:erased a)
           (_:squash (fact v))
  = MHR.witness r (lift_property fact) (hide (U.raise_val (reveal v))) ()

/// If we previously witnessed the validity of [fact], we can recall its validity
let recall (#inames: _)
           (#a:Type u#0)
           (#q:perm)
           (#p:Preorder.preorder a)
           (fact:property a)
           (r:erased (ref a p))
           (v:erased a)
           (w:witnessed r fact)
  = MHR.recall (lift_property fact) r (hide (U.raise_val (reveal v))) w

/// Monotonic references are also equipped with the usual fractional permission discipline
/// So, you can split a reference into two read-only shares
let share (#inames:_)
          (#a:Type)
          (#p:Preorder.preorder a)
          (r:ref a p)
          (f:perm)
          (v:Ghost.erased a)
  : SteelGhostT unit inames
    (pts_to r f v)
    (fun _ -> pts_to r (half_perm f) v `star` pts_to r (half_perm f) v)
  = MHR.share r f (hide (U.raise_val (reveal v)))

/// And you can gather back the shares
let gather (#inames:_)
           (#a:Type)
           (#p:Preorder.preorder a)
           (r:ref a p)
           (f g:perm)
           (v:Ghost.erased a)
  : SteelGhostT unit inames
    (pts_to r f v `star` pts_to r g v)
    (fun _ -> pts_to r (sum_perm f g) v)
  = MHR.gather r f g (hide (U.raise_val (reveal v)))

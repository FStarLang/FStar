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

module Steel.GhostMonotonicHigherReference

open FStar.Ghost
open FStar.PCM
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.GhostPCMReference
open Steel.FractionalPermission
open Steel.Preorder

module Preorder = FStar.Preorder
module Q = Steel.Preorder
module M = Steel.Memory
module PR = Steel.GhostPCMReference
module A = Steel.Effect.Atomic
open FStar.Real

#set-options "--ide_id_info_off"

let ref a p = PR.ref (history a p) pcm_history

[@@__reduce__]
let pts_to_body #a #p (r:ref a p) (f:perm) (v:a) (h:history a p) =
      PR.pts_to r h `star`
      pure (history_val h v f)

let pts_to' (#a:Type) (#p:Preorder.preorder a) (r:ref a p) (f:perm) (v: a) =
    h_exists (pts_to_body r f v)

let pts_to_sl r f v = hp_of (pts_to' r f v)

let intro_pure #opened #a #p #f
                 (r:ref a p)
                 (v:a)
                 (h:history a p { history_val h v f })
  : SteelGhostT unit opened
           (PR.pts_to r h)
           (fun _ -> pts_to_body r f v h)
  = A.intro_pure (history_val h v f)

let intro_pure_full #opened #a #p #f
                 (r:ref a p)
                 (v:a)
                 (h:history a p { history_val h v f })
  : SteelGhostT unit opened
           (PR.pts_to r h)
           (fun _ -> pts_to r f v)
  = intro_pure #_ #a #p #f r v h;
    intro_exists h (pts_to_body r f v)

let alloc #_ (#a:Type) (p:Preorder.preorder a) (v:a)
  = let h = Current [v] full_perm in
    assert (compatible pcm_history h h);
    let x : ref a p = alloc h in
    intro_pure_full x v h;
    x

let extract_pure #a #uses #p #f
                 (r:ref a p)
                 (v:a)
                 (h:(history a p))
  : SteelGhostT (_:unit{history_val h v f})
           uses
           (pts_to_body r f v h)
           (fun _ -> pts_to_body r f v h)
  = elim_pure (history_val h v f);
    A.intro_pure (history_val h v f)

let elim_pure #a #uses #p #f
                 (r:ref a p)
                 (v:a)
                 (h:(history a p))
  : SteelGhostT (_:unit{history_val h v f})
           uses
           (pts_to_body r f v h)
           (fun _ ->  PR.pts_to r h)
  = let _ = extract_pure r v h in
    drop (pure (history_val h v f))

let write (#opened: _) (#a:Type) (#p:Preorder.preorder a) (#v:a)
          (r:ref a p) (x:a)
  : SteelGhost unit opened (pts_to r full_perm v)
               (fun v -> pts_to r full_perm x)
               (requires fun _ -> p v x /\ True)
               (ensures fun _ _ _ -> True)
  = let h_old_e = witness_exists #_ #_ #(pts_to_body r full_perm v) () in
    let _ = elim_pure r v h_old_e in

    let h_old = read r in
    let h: history a p = extend_history' h_old x in
    write r h_old_e h;

    intro_pure_full r x h

let witnessed #a #p r fact =
  PR.witnessed r (lift_fact fact)

let get_squash (#p:prop) (_:unit{p}) : squash p = ()

let witness_thunk (#inames: _) (#a:Type) (#pcm:FStar.PCM.pcm a)
                  (r:PR.ref a pcm)
                  (fact:M.stable_property pcm)
                  (v:erased a)
                  (sq:squash (fact_valid_compat #_ #pcm fact v))
                  (_:unit)
  : SteelAtomicUT (PR.witnessed r fact) inames
                  (PR.pts_to r v)
                  (fun _ -> PR.pts_to r v)
  = witness r fact v sq

let witness (#inames: _) (#a:Type) (#q:perm) (#p:Preorder.preorder a)
            (r:ref a p)
            (fact:stable_property p)
            (v:erased a)
            (_:squash (fact v))
  : SteelAtomicUT (witnessed r fact) inames
                  (pts_to r q v)
                  (fun _ -> pts_to r q v)
  = let h = witness_exists #_ #_ #(pts_to_body r q v) () in
    let _ = elim_pure #_ #_ #_ #q r v h in

    assert (forall h'. compatible pcm_history h h' ==> lift_fact fact h');
    lift_fact_is_stable #a #p fact;

    let w = witness_thunk #_ #_ #(pcm_history #a #p)  r (lift_fact fact) h () () in

  
    intro_pure_full r v h;
    rewrite_slprop (pts_to _ q _) (pts_to r q v) (fun _ -> ());
    return w

let recall (#inames: _) (#a:Type u#1) (#q:perm) (#p:Preorder.preorder a) (fact:property a)
           (r:ref a p) (v:erased a) (w:witnessed r fact)
  = let h = witness_exists #_ #_ #(pts_to_body r q v) () in
    let _ = elim_pure #_ #_ #_ #q r v h in

    let h1 = recall (lift_fact fact) r h w in

    intro_pure_full r v h;
    rewrite_slprop (pts_to _ q _) (pts_to r q v) (fun _ -> ())

let elim_pts_to #o (#a:Type)
                (#p:Preorder.preorder a)
                (r:ref a p)
                (f:perm)
                (v:a)
    : SteelGhostT unit o
                  (pts_to r f v)
                  (fun _ -> pts_to' r f v)
    = rewrite_slprop _ _ (fun _ -> ())


let intro_pts_to #o (#a:Type)
                (#p:Preorder.preorder a)
                (r:ref a p)
                (f:perm)
                (v:a)
    : SteelGhostT unit o
                  (pts_to' r f v)
                  (fun _ -> pts_to' r f v)
    = rewrite_slprop _ _ (fun _ -> ())

let share #o (#a:Type) (#p:Preorder.preorder a) (r:ref a p) (f:perm) (v:a)
  : SteelGhostT unit o
    (pts_to r f v)
    (fun _ -> pts_to r (half_perm f) v `star` pts_to r (half_perm f) v)
  = let open Steel.Effect.Atomic in
    elim_pts_to r f v;
    let h : erased (history a p) = witness_exists () in
    elim_pure _;
    let sh = split_current h in
    PR.share r h sh sh;
    intro_pure (history_val sh v (half_perm f));
    intro_exists #(history a p) sh (pts_to_body r (half_perm f) v);
    intro_pts_to r (half_perm f) v;
    intro_pure (history_val sh v (half_perm f));
    intro_exists #(history a p) sh (pts_to_body r (half_perm f) v);
    intro_pts_to r (half_perm f) v

let gather #o (#a:Type) (#p:Preorder.preorder a) (r:ref a p) (f g:perm) (v:a)
  : SteelGhostT unit o
    (pts_to r f v `star` pts_to r g v)
    (fun _ -> pts_to r (sum_perm f g) v)
  = let open Steel.Effect.Atomic in
    elim_pts_to r f v;
    let hf : erased (history a p) = witness_exists #_ #_ #(pts_to_body r f v) () in
    elim_pure _;
    elim_pts_to r g v;
    let hg : erased (history a p) = witness_exists () in
    elim_pure _;
    PR.gather r hf hg;
    intro_pure (history_val (op pcm_history hf hg) v (sum_perm f g));
    intro_exists (op pcm_history hf hg) (pts_to_body r (sum_perm f g) v);
    intro_pts_to r (sum_perm f g) v

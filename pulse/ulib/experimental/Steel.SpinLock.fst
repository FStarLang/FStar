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

module Steel.SpinLock
open Steel.Effect
open Steel.Effect.Atomic
open Steel.Permissions
open Steel.Reference
open Steel.Actions
open Steel.SteelT.Basics
open Steel.SteelAtomic.Basics
open Steel.Memory.Tactics

module U = FStar.Universe

let available = false
let locked = true

let lockinv (p:hprop) (r:ref bool) : hprop =
  h_exists (fun b -> pts_to r full_perm (Ghost.hide b) `star` (if b then emp else p))

let lock (p:hprop u#1) = (r:ref bool) & ival (lockinv p r)

val intro_lockinv_available (#uses:Set.set lock_addr) (p:hprop) (r:ref bool)
  : SteelAtomic unit uses true (pts_to r full_perm available `star` p) (fun _ -> lockinv p r)

val intro_lockinv_locked (#uses:Set.set lock_addr) (p:hprop) (r:ref bool)
  : SteelAtomic unit uses true (pts_to r full_perm locked) (fun _ -> lockinv p r)

let intro_lockinv_available #uses p r =
  intro_h_exists (U.raise_val false)
    (fun (b: U.raise_t bool) ->
      pts_to r full_perm (Ghost.hide (U.downgrade_val  b)) `star`
        (if (U.downgrade_val b) then emp else p)
    )

let intro_lockinv_locked #uses p r =
  h_intro_emp_l (pts_to r full_perm locked);
  h_commute emp (pts_to r full_perm locked);
  intro_h_exists (U.raise_val true)
    (fun b -> pts_to r full_perm (Ghost.hide (U.downgrade_val b)) `star`
      (if (U.downgrade_val b) then emp else p))

val new_inv (p:hprop) : SteelT (ival p) p (fun _ -> emp)
let new_inv p = lift_atomic_to_steelT (fun _ -> Steel.Effect.Atomic.new_inv p)

#set-options "--fuel 0 --ifuel 0"

let new_lock (p:hprop)
  : SteelT (lock p) p (fun _ -> emp) =
  Steel.SteelT.Basics.h_intro_emp_l p;
  let r:ref bool =
    steel_frame_t (fun _ -> alloc available) // p
  in
  lift_atomic_to_steelT (fun _ -> intro_lockinv_available p r);
  let i:ival (lockinv p r) = new_inv (lockinv p r) in
  let l:lock p = (| r, i |) in
  l

#set-options "--fuel 0 --ifuel 0"
val cas_frame
  (#t:eqtype)
  (#uses:Set.set lock_addr)
  (r:ref t)
  (v:Ghost.erased t)
  (v_old:t)
  (v_new:t)
  (frame:hprop)
  : SteelAtomic
    (b:bool{b <==> (Ghost.reveal v == v_old)})
    uses
    false
    (pts_to r full_perm v `star` frame)
    (fun b -> (if b then pts_to r full_perm v_new else pts_to r full_perm v) `star` frame)
let cas_frame #t #uses r v v_old v_new frame =
  atomic_frame frame (fun _ ->
    let x = Steel.Effect.Atomic.cas r v v_old v_new in
    return_atomic x
  )

val acquire_core (#p:hprop) (#u:Set.set lock_addr) (r:ref bool) (i:ival (lockinv p r))
  : SteelAtomic bool u false
    (lockinv p r `star` emp)
    (fun b -> lockinv p r `star` (if b then p else emp))

let acquire_core #p #u r i =
  h_commute (lockinv p r) emp;
  h_elim_emp_l (lockinv p r);
  let ghost = ghost_read_refine r (fun b -> if b then emp else p) in

  let frame = if ghost then emp else p in

  let res = cas_frame r ghost available locked frame in

  atomic_frame (if ghost then emp else p) (fun _ -> intro_lockinv_locked p r);

  return_atomic #_ #_ #(fun b -> lockinv p r `star` (if b then p else emp)) res

let acquire' (#p:hprop) (l:lock p)
  : SteelAtomic bool Set.empty false emp (fun b -> if b then p else emp)
  = let r:ref bool = dfst l in
    let i: ival (lockinv p r) = dsnd l in
    let b = with_invariant_frame i (fun _ -> acquire_core r i) in
    return_atomic #_ #_ #_ b

let rec acquire #p l =
  let b = lift_atomic_to_steelT (fun _ -> acquire' l) in
  cond b (fun b -> if b then p else emp) (fun _ _ -> p) noop (fun _ -> acquire l)

val release_core (#p:hprop) (#u:Set.set lock_addr) (r:ref bool) (i:ival (lockinv p r))
  : SteelAtomic bool u false
    (lockinv p r `star` p)
    (fun b -> lockinv p r `star` (if b then emp else p))

let release_core #p #u r i =
  h_assert_atomic (h_exists (fun b -> pts_to r full_perm (Ghost.hide b) `star` (if b then emp else p))
    `star` p);
  let v:bool = atomic_frame p (fun _ ->  ghost_read_refine r (fun b -> if b then emp else p)) in
  h_assert_atomic ((pts_to r full_perm (Ghost.hide v) `star` (if v then emp else p)) `star` p);
  h_assoc_left (pts_to r full_perm (Ghost.hide v)) (if v then emp else p) p;
  let res = cas_frame r v locked available ((if v then emp else p) `star` p) in
  h_assert_atomic (pts_to r full_perm available `star` ((if res then emp else p) `star` p));
  h_commute (pts_to r full_perm available) ((if res then emp else p) `star` p);
  atomic_frame (pts_to r full_perm available) (fun _ -> h_commute (if res then emp else p) p);
  h_commute (p `star` (if res then emp else p)) (pts_to r full_perm available);
  h_assoc_right (pts_to r full_perm available) p (if res then emp else p);
  atomic_frame (if res then emp else p) (fun _ -> intro_lockinv_available p r);
  return_atomic #_ #_ #_ res

let release #p l =
  let r:ref bool = dfst l in
  let i: ival (lockinv p r) = dsnd l in
  let b = lift_atomic_to_steelT (fun _ -> with_invariant_frame i
    (fun _ -> release_core r i))
  in
  Steel.SteelT.Basics.h_intro_emp_l (if b then emp else p);
  Steel.SteelT.Basics.h_affine emp (if b then emp else p)

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

open FStar.Ghost
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
open Steel.FractionalPermission
module Atomic = Steel.Effect.Atomic

#set-options "--ide_id_info_off --fuel 0 --ifuel 0"

let available = false
let locked = true

let lockinv (p:slprop) (r:ref bool) : slprop =
  h_exists (fun b -> pts_to r full_perm (Ghost.hide b) `star` (if b then emp else p))

let lock_t = ref bool & erased iname

let protects (l:lock_t) (p:slprop) : prop = snd l >--> lockinv p (fst l)

val intro_lockinv_available (#uses:inames) (p:slprop) (r:ref bool)
  : SteelGhostT unit uses (pts_to r full_perm available `star` p) (fun _ -> lockinv p r)

val intro_lockinv_locked (#uses:inames) (p:slprop) (r:ref bool)
  : SteelGhostT unit uses (pts_to r full_perm locked) (fun _ -> lockinv p r)

let intro_lockinv_available #uses p r =
  intro_exists false
    (fun (b: bool) ->
      pts_to r full_perm (Ghost.hide b) `star`
        (if b then emp else p)
    )

let intro_lockinv_locked #uses p r =
  intro_exists true
    (fun b -> pts_to r full_perm (Ghost.hide b) `star`
          (if b then emp else p))

val new_inv (p:slprop) : SteelT (inv p) p (fun _ -> emp)
let new_inv p = new_invariant Set.empty p

let new_lock (p:slprop)
  : SteelT (lock p) p (fun _ -> emp) =
  let r = alloc available in
  intro_lockinv_available p r;
  let i:inv (lockinv p r) = new_inv (lockinv p r) in
  (r, i)

val acquire_core (#p:slprop) (#u:inames) (r:ref bool) (i:inv (lockinv p r))
  : SteelAtomicT bool u
    (lockinv p r `star` emp)
    (fun b -> lockinv p r  `star` (if b then p else emp))

let acquire_core #p #u r i =
  let ghost = witness_h_exists () in

  let res = cas r ghost available locked in

  (* Not sure we can avoid calling an SMT here. Better force the manual call? *)
  change_slprop (if (Ghost.reveal ghost) then emp else p) (if res then p else emp)
    (fun _ -> ());
  change_slprop (if res then pts_to r full_perm (Ghost.hide locked) else pts_to r full_perm ghost) (pts_to r full_perm locked) (fun _ -> ());

  intro_lockinv_locked p r;
  return res

let rec acquire #p l =
  let r:ref bool = fst l in
  let i: inv (lockinv p r) = snd l in
  let b = with_invariant i (fun _ -> acquire_core r i) in
  if b then (
    change_slprop (if b then p else emp) p (fun _ -> ());
    noop ()
  ) else (
    change_slprop (if b then p else emp) emp (fun _ -> ());
    acquire l
  )

val release_core (#p:slprop) (#u:inames) (r:ref bool) (i:inv (lockinv p r))
  : SteelAtomicT bool u
    (lockinv p r `star` p)
    (fun b -> lockinv p r `star` (if b then emp else p))

let release_core #p #u r i =
  let v = witness_h_exists () in

  let res = cas r v locked available in

  (* Not sure we can avoid calling an SMT here. Better force the manual call? *)
  change_slprop (if (Ghost.reveal v) then emp else p) (if res then emp else p)
    (fun _ -> ());
  change_slprop (if res then pts_to r full_perm (Ghost.hide available) else pts_to r full_perm v) (pts_to r full_perm available) (fun _ -> ());

  intro_lockinv_available p r;
  return res

let release (#p:slprop) (l:lock p) =
  let r:ref bool = fst l in
  let i: inv (lockinv p r) = snd l in
  let b = with_invariant i (fun _ -> release_core r i) in
  drop (if b then emp else p)

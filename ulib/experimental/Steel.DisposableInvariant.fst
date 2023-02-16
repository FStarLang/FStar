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

module Steel.DisposableInvariant

open FStar.Ghost
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference

#push-options "--ide_id_info_off"

[@@__reduce__]
let conditional_inv (r:ghost_ref bool) (p:vprop) =
      (fun (b:bool) ->
         ghost_pts_to r (half_perm full_perm) b `star`
         (if b then p else emp))

[@@__reduce__]
let ex_conditional_inv (r:ghost_ref bool) (p:vprop) =
    h_exists (conditional_inv r p)

let inv (p:vprop) = r:ghost_ref bool & inv (ex_conditional_inv r p)

let name (#p:_) (i:inv p) = name_of_inv (dsnd i)
let gref (#p:_) (i:inv p) = dfst i

[@@__reduce__]
let active (#p:_) ([@@@smt_fallback]f:perm) (i:inv p) =
  ghost_pts_to (gref i) (half_perm f) true

let new_inv #u p =
  let r = ghost_alloc_pt (Ghost.hide true) in
  ghost_share_pt r;
  intro_exists true (conditional_inv r p);
  let i = new_invariant (ex_conditional_inv r p) in
  rewrite_slprop
    (ghost_pts_to r (half_perm full_perm) true)
    (ghost_pts_to (gref (hide (| r, i |))) (half_perm full_perm) true)
    (fun _ -> ());
  return (| r, i |)

let share #p #f #u i = ghost_share_pt #_ #_ #_ #(hide true) (gref i)

let gather #p #f0 #f1 #u i =
  ghost_gather_pt #_ #_ #(half_perm f0) (gref i);
  rewrite_slprop
    (ghost_pts_to (gref i) (sum_perm (half_perm f0) (half_perm f1)) (hide true))
    (ghost_pts_to (gref i) (half_perm (sum_perm f0 f1)) (hide true))
    (fun _ -> assert (FStar.Real.two == 2.0R); assert (sum_perm (half_perm f0) (half_perm f1) == (half_perm (sum_perm f0 f1))))

let dispose #p #u i
  : SteelAtomicUT unit u
    (active full_perm i)
    (fun _ -> p)
  = let dispose_aux (r:ghost_ref bool) (_:unit)
    : SteelGhostT unit (add_inv u i)
       (ex_conditional_inv r p `star`
        ghost_pts_to r (half_perm full_perm) true)
       (fun _ ->
        ex_conditional_inv r p `star`
        p)
    = let b = witness_exists #_ #_ #(conditional_inv r p) () in
      ghost_gather_pt #_ #_ #_ #_ #true #(hide (reveal b)) r;
      rewrite_slprop (if b then p else emp) p (fun _ -> ());
      rewrite_slprop (ghost_pts_to r (sum_perm (half_perm full_perm) (half_perm full_perm)) true)
                      (ghost_pts_to r full_perm true)
                      (fun _ -> ());
      ghost_write_pt r false;
      ghost_share_pt r;
      intro_exists false (conditional_inv r p);
      drop (ghost_pts_to r (half_perm full_perm) false)
    in
    let x = with_invariant_g (dsnd i)
                             (dispose_aux (gref i)) in
    ()

let with_invariant #a #fp #fp' #u #obs #p #perm i f
  = let with_invariant_aux (r:ghost_ref bool)
                           (_:unit)
      : SteelAtomicBaseT a (add_inv u i) obs
          (ex_conditional_inv r p `star`
            (ghost_pts_to r (half_perm perm) true `star`
          fp))
          (fun x ->
            ex_conditional_inv r p `star`
          (ghost_pts_to r (half_perm perm) true `star` //associativity matters
          fp' x))
    = let b = witness_exists #_ #_ #(conditional_inv r p) () in
      ghost_pts_to_injective_eq r true (hide (reveal b));
      rewrite_slprop (if b then p else emp) p (fun _ -> ());
      let x = f() in
      intro_exists true (conditional_inv r p);
      return x
    in
    with_invariant (dsnd i)
                   (with_invariant_aux (gref i))

let with_invariant_g #a #fp #fp' #u #p #perm i f
  = let with_invariant_aux (r:ghost_ref bool)
                           (_:unit)
      : SteelGhostT a (add_inv u i)
          (ex_conditional_inv r p `star`
            (ghost_pts_to r (half_perm perm) true `star`
          fp))
          (fun x ->
            ex_conditional_inv r p `star`
          (ghost_pts_to r (half_perm perm) true `star` //associativity matters
          fp' x))
    = let b = witness_exists #_ #_ #(conditional_inv r p) () in
      ghost_pts_to_injective_eq r true (hide (reveal b));
      rewrite_slprop (if b then p else emp) p (fun _ -> ());
      let x = f() in
      intro_exists true (conditional_inv r p);
      x
    in
    let x = with_invariant_g (dsnd i)
                             (with_invariant_aux (gref i)) in
    x

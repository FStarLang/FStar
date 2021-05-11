module Steel.DisposableInvariant

open FStar.Ghost
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Memory
open Steel.FractionalPermission
module A = Steel.Effect.Atomic
#push-options "--ide_id_info_off"
open Steel.Reference

[@@__reduce__]
let conditional_inv (r:ghost_ref bool) (p:slprop) =
      (fun (b:bool) ->
         ghost_pts_to r (half_perm full_perm) (hide b) `star`
         (if b then p else emp))

[@@__reduce__]
let ex_conditional_inv (r:ghost_ref bool) (p:slprop) =
    h_exists (conditional_inv r p)

let inv (p:slprop) = erased (r:ghost_ref bool & Steel.Memory.inv (ex_conditional_inv r p))

let name (#p:_) (i:inv p) = dsnd i
let gref (#p:_) (i:inv p) = dfst i

[@@__reduce__]
let active (#p:_) ([@@@smt_fallback]f:perm) (i:inv p) =
  ghost_pts_to (gref i) (half_perm f) (hide true)

let new_inv #u p =
  let r = ghost_alloc (Ghost.hide true) in
  ghost_share r;
  A.intro_exists true (conditional_inv r p);
  let i = A.new_invariant (ex_conditional_inv r p) in
  rewrite_context ();  //TODO: this is rewriting gref (hide (| r, x |)) to r, revisit
  (| r, i |)

let share #p #f #u i = ghost_share (gref i)

let gather #p #f0 #f1 #u i =
  ghost_gather #_ #_ #(half_perm f0) (gref i);
  A.change_slprop
    (ghost_pts_to (gref i) (sum_perm (half_perm f0) (half_perm f1)) (hide true))
    (ghost_pts_to (gref i) (half_perm (sum_perm f0 f1)) (hide true))
    (fun _ -> assert (FStar.Real.two == 2.0R); assert (sum_perm (half_perm f0) (half_perm f1) == (half_perm (sum_perm f0 f1))))

let dispose #p #u i
  : SteelGhostT unit u
    (active full_perm i)
    (fun _ -> p)
  = let dispose_aux (r:ghost_ref bool) (_:unit)
    : SteelGhostT unit (add_inv u i)
       (ex_conditional_inv r p `star`
        ghost_pts_to r (half_perm full_perm) true)
       (fun _ ->
        ex_conditional_inv r p `star`
        p)
    = let b = A.witness_h_exists #_ #_ #(conditional_inv r p) () in
      ghost_gather #_ #_ #_ #_ #true #(hide (reveal b)) r;
      A.change_slprop (if b then p else emp) p (fun _ -> ());
      A.change_slprop (ghost_pts_to r (sum_perm (half_perm full_perm) (half_perm full_perm)) true)
                      (ghost_pts_to r full_perm true)
                      (fun _ -> ());
      ghost_write r false;
      ghost_share r;
      A.intro_exists false (conditional_inv r p);
      drop (ghost_pts_to r (half_perm full_perm) false)
    in
    A.with_invariant_g (name i)
                       (dispose_aux (gref i))

let with_invariant #a #fp #fp' #u #p #perm i f
  = let with_invariant_aux (r:ghost_ref bool)
                           (_:unit)
      : SteelAtomicT a (add_inv u i)
          (ex_conditional_inv r p `star`
            (ghost_pts_to r (half_perm perm) true `star`
          fp))
          (fun x ->
            ex_conditional_inv r p `star`
          (ghost_pts_to r (half_perm perm) true `star` //associativity matters
          fp' x))
    = let b = A.witness_h_exists #_ #_ #(conditional_inv r p) () in
      ghost_pts_to_injective_eq r true (hide (reveal b));
      A.change_slprop (if b then p else emp) p (fun _ -> ());
      let x = f() in
      A.intro_exists true (conditional_inv r p);
      return x
    in
    A.with_invariant (name i)
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
    = let b = A.witness_h_exists #_ #_ #(conditional_inv r p) () in
      ghost_pts_to_injective_eq r true (hide (reveal b));
      A.change_slprop (if b then p else emp) p (fun _ -> ());
      let x = f() in
      A.intro_exists true (conditional_inv r p);
      x
    in
    A.with_invariant_g (name i)
                       (with_invariant_aux (gref i))

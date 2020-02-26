module Steel.SpinLock
open Steel.Effect
open Steel.Effect.Atomic
open Steel.Permissions
open Steel.Reference
open Steel.Actions
open Steel.SteelT.Basics
open Steel.SteelAtomic.Basics

let available = false
let locked = true

let lockinv (p:hprop) (r:ref bool) : hprop =
  h_exists (fun b -> pts_to r full_permission (Ghost.hide b) `star` (if b then emp else p))
//  h_or (pts_to r full_permission available `star` p) (pts_to r full_permission locked `star` emp)

let lock (p:hprop) = (r:ref bool) & inv (lockinv p r)

val intro_lockinv_available (#uses:Set.set lock_addr) (p:hprop) (r:ref bool)
  : SteelAtomic unit uses true (pts_to r full_permission available `star` p) (fun _ -> lockinv p r)

val intro_lockinv_locked (#uses:Set.set lock_addr) (p:hprop) (r:ref bool)
  : SteelAtomic unit uses true (pts_to r full_permission locked) (fun _ -> lockinv p r)

let intro_lockinv_available #uses p r =
  intro_h_exists false
    (fun b -> pts_to r full_permission (Ghost.hide b) `star` (if b then emp else p))

let intro_lockinv_locked #uses p r =
  h_intro_emp_l (pts_to r full_permission locked);
  h_commute emp (pts_to r full_permission locked);
  intro_h_exists true
    (fun b -> pts_to r full_permission (Ghost.hide b) `star` (if b then emp else p))

val new_inv (p:hprop) : SteelT (inv p) p (fun _ -> emp)
let new_inv p = lift_atomic_to_steelT (fun _ -> Steel.Effect.Atomic.new_inv p)

let new_lock (p:hprop)
  : SteelT (lock p) p (fun _ -> emp) =
  let r:ref bool =
    steel_frame_t (fun _ -> alloc available) in
  lift_atomic_to_steelT (fun _ -> intro_lockinv_available p r);
  let i:inv (lockinv p r) = new_inv (lockinv p r) in
  let l:lock p = (| r, i |) in
  l

val acquire_core (#p:hprop) (#u:Set.set lock_addr) (r:ref bool) (i:inv (lockinv p r))
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
    let i: inv (lockinv p r) = dsnd l in
    let b = with_invariant_frame i (fun _ -> acquire_core r i) in
    return_atomic #_ #_ #_ b

let rec acquire #p l =
  let b = lift_atomic_to_steelT (fun _ -> acquire' l) in
  cond b (fun b -> if b then p else emp) (fun _ _ -> p) noop (fun _ -> acquire l)

assume
val non_duplicable (#p:hprop) (#u:Set.set lock_addr) (r:ref bool) (i:inv (lockinv p r))
  : SteelAtomic unit u true
    (lockinv p r `star` p)
    (fun _ -> pts_to r full_permission locked `star` p)

val release_core (#p:hprop) (#u:Set.set lock_addr) (r:ref bool) (i:inv (lockinv p r))
  : SteelAtomic unit u false
    (lockinv p r `star` p)
    (fun _ -> lockinv p r `star` emp)

let release_core #p #u r i =
  non_duplicable r i;
  let v:bool = atomic_frame p (fun _ -> ghost_read r) in
  let res = cas_frame r v locked available p in
  h_assert_atomic (pts_to r full_permission available `star` p);
  intro_lockinv_available p r;
  h_intro_emp_l (lockinv p r);
  h_commute emp (lockinv p r)

let release #p l =
  let r:ref bool = dfst l in
  let i: inv (lockinv p r) = dsnd l in
  let b = lift_atomic_to_steelT (fun _ -> with_invariant_frame i
    (fun _ -> release_core r i))
  in ()

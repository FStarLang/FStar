module Steel.SpinLock
open Steel.Effect
open Steel.Effect.Atomic
open Steel.Permissions
open Steel.Reference
open Steel.Actions
open FStar.Ghost

let available = false
let locked = true

unfold
let lockinv (p:hprop) (r:ref bool) : hprop =
  h_or (pts_to r full_permission available `star` p) (pts_to r full_permission locked `star` emp)

let lock (p:hprop) = (r:ref bool) & inv (lockinv p r)

assume
val h_admit (#a:_) (p:hprop) (q:a -> hprop)
  : SteelT a p q

assume
val h_admit_atomic (#a:_) (#uses:Set.set lock_addr) (p:hprop) (q:a -> hprop)
  : SteelAtomic a uses true p q


assume
val h_assert (p:hprop)
  : SteelT unit p (fun _ -> p)

assume
val h_assert_atomic (#uses:Set.set lock_addr) (p:hprop)
  : SteelAtomic unit uses true p (fun _ -> p)

assume
val h_intro_emp_l (p:hprop)
  : SteelAtomic unit Set.empty true p (fun _ -> emp `star` p)

assume
val h_commute (p q:hprop)
  : SteelAtomic unit Set.empty true (p `star` q) (fun _ -> q `star` p)


assume
val intro_h_or_left (p:hprop) (q:hprop)
  : SteelT unit p (fun _ -> h_or p q)

assume
val intro_h_or_right (p:hprop) (q:hprop)
  : SteelAtomic unit Set.empty true q (fun _ -> h_or p q)

val intro_lockinv_left (p:hprop) (r:ref bool)
  : SteelT unit (pts_to r full_permission available `star` p) (fun _ -> lockinv p r)

val intro_lockinv_right (p:hprop) (r:ref bool)
  : SteelAtomic unit Set.empty true (pts_to r full_permission locked) (fun _ -> lockinv p r)

let intro_lockinv_left p r =
  intro_h_or_left
    (pts_to r full_permission available `star` p)
    (pts_to r full_permission locked `star` emp)

let intro_lockinv_right p r =
  h_intro_emp_l (pts_to r full_permission locked);
  h_commute emp (pts_to r full_permission locked);
  intro_h_or_right
    (pts_to r full_permission available `star` p)
    (pts_to r full_permission locked `star` emp)

assume
val lift_atomic_to_steelT
  (#a:Type) (#is_ghost:bool) (#fp:hprop) (#fp':a -> hprop)
  ($f:unit -> SteelAtomic a Set.empty is_ghost fp fp')
  : SteelT a fp fp'

val new_inv (p:hprop) : SteelT (inv p) p (fun _ -> emp)
let new_inv p = lift_atomic_to_steelT (fun _ -> Steel.Effect.Atomic.new_inv p)

let new_lock (p:hprop)
  : SteelT (lock p) p (fun _ -> emp) =
  let r:ref bool =
    steel_frame_t (fun _ -> alloc available) in
  intro_lockinv_left p r;
  let i:inv (lockinv p r) = new_inv (lockinv p r) in
  let l:lock p = (| r, i |) in
  l

/// A specialized version of get_ref_refine. It should be derivable from h_exists
assume
val ghost_read_or (#uses:Set.set lock_addr) (#p:perm) (r:ref bool)
  (q:bool -> hprop)
  : SteelAtomic bool uses true
    (h_or (pts_to r p false `star` q false) (pts_to r p true `star` q true))
    (fun x -> pts_to r p x `star` q x)

assume
val cas
  (#t:eqtype)
  (#uses:Set.set lock_addr)
  (r:ref t)
  (v:Ghost.erased t)
  (v_old:t)
  (v_new:t)
  : SteelAtomic
    (b:bool{b <==> (Ghost.reveal v == v_old)})
    uses
    false
    (pts_to r full_permission v)
    (fun b -> if b then pts_to r full_permission v_new else pts_to r full_permission v)

assume
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
    (pts_to r full_permission v `star` frame)
    (fun b -> (if b then pts_to r full_permission v_new else pts_to r full_permission v) `star` frame)


assume
val atomic_frame (#a:Type) (#pre:pre_t) (#post:post_t a)
          (#uses:Set.set lock_addr) (#is_ghost:bool)
          (frame:hprop)
          ($f:unit -> SteelAtomic a uses is_ghost pre post)
  : SteelAtomic a
    uses is_ghost
    (pre `star` frame)
    (fun x -> post x `star` frame)

val acquire_core (#p:hprop) (r:ref bool) (i:inv (lockinv p r))
  : SteelAtomic bool Set.empty false
    (lockinv p r)
    (fun b -> lockinv p r `star` (if b then p else emp))

let acquire_core #p r i =
  let ghost = ghost_read_or r (fun b -> if b then emp else p) in
  let frame = if ghost then emp else p in

  let res = cas_frame r ghost available locked frame in

  atomic_frame (if ghost then emp else p) (fun _ -> intro_lockinv_right p r);

  h_assert_atomic (lockinv p r `star` (if res then p else emp));

  h_admit_atomic
    (lockinv p r `star` (if res then p else emp))
    (fun b -> lockinv p r `star` (if b then p else emp))

//TODO : Why is this failing? We have the postresource in the context
//  res


let acquire (#p:hprop) (l:lock p)
  : SteelT unit emp (fun _ -> p)
  = h_admit emp (fun _ -> p)

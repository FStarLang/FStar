module Steel.SpinLock
open Steel.Effect
open Steel.Effect.Atomic
open Steel.Permissions
open Steel.Reference
open Steel.Actions

let available = false
let locked = true

let lockinv (p:hprop) (r:ref bool) : hprop =
  // h_exists (fun b -> pts_to r full_permission b `star` (if b then emp else p))
  h_or (pts_to r full_permission available `star` p) (pts_to r full_permission locked `star` emp)

let lock (p:hprop) = (r:ref bool) & inv (lockinv p r)

assume
val return_atomic (#a:Type) (#uses:Set.set lock_addr) (#p:a -> hprop) (x:a)
  : SteelAtomic a uses true (p x) p

assume
val noop_t (#p:hprop) (u:unit) : SteelT unit p (fun _ -> p)

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
val h_intro_emp_l (#uses:Set.set lock_addr) (p:hprop)
  : SteelAtomic unit uses true p (fun _ -> emp `star` p)

assume
val h_elim_emp_l (#uses:Set.set lock_addr) (p:hprop)
  : SteelAtomic unit uses true (emp `star` p) (fun _ -> p)


assume
val h_commute (#uses:Set.set lock_addr) (p q:hprop)
  : SteelAtomic unit uses true (p `star` q) (fun _ -> q `star` p)


assume
val intro_h_or_left (#uses:Set.set lock_addr) (p:hprop) (q:hprop)
  : SteelAtomic unit uses true p (fun _ -> h_or p q)

assume
val intro_h_or_right (#uses:Set.set lock_addr) (p:hprop) (q:hprop)
  : SteelAtomic unit uses true q (fun _ -> h_or p q)

val intro_lockinv_left (#uses:Set.set lock_addr) (p:hprop) (r:ref bool)
  : SteelAtomic unit uses true (pts_to r full_permission available `star` p) (fun _ -> lockinv p r)

val intro_lockinv_right (#uses:Set.set lock_addr) (p:hprop) (r:ref bool)
  : SteelAtomic unit uses true (pts_to r full_permission locked) (fun _ -> lockinv p r)

let intro_lockinv_left #uses p r =
  intro_h_or_left
    (pts_to r full_permission available `star` p)
    (pts_to r full_permission locked `star` emp)

let intro_lockinv_right #uses p r =
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
  lift_atomic_to_steelT (fun _ -> intro_lockinv_left p r);
  let i:inv (lockinv p r) = new_inv (lockinv p r) in
  let l:lock p = (| r, i |) in
  l

assume
val ghost_read (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (#v:Ghost.erased a) (r:ref a)
  : SteelAtomic a uses true
    (pts_to r p v)
    (fun x -> pts_to r p x)


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

val acquire_core (#p:hprop) (#u:Set.set lock_addr) (r:ref bool) (i:inv (lockinv p r))
  : SteelAtomic bool u false
    (lockinv p r `star` emp)
    (fun b -> lockinv p r `star` (if b then p else emp))

let acquire_core #p #u r i =
  h_commute (lockinv p r) emp;
  h_elim_emp_l (lockinv p r);
  let ghost = ghost_read_or r (fun b -> if b then emp else p) in

  let frame = if ghost then emp else p in

  let res = cas_frame r ghost available locked frame in

  atomic_frame (if ghost then emp else p) (fun _ -> intro_lockinv_right p r);

  return_atomic #_ #_ #(fun b -> lockinv p r `star` (if b then p else emp)) res

let acquire' (#p:hprop) (l:lock p)
  : SteelAtomic bool Set.empty false emp (fun b -> if b then p else emp)
  = let r:ref bool = dfst l in
    let i: inv (lockinv p r) = dsnd l in
    let b = with_invariant_frame i (fun _ -> acquire_core r i) in
    return_atomic #_ #_ #_ b

let rec acquire #p l =
  let b = lift_atomic_to_steelT (fun _ -> acquire' l) in
  cond b (fun b -> if b then p else emp) (fun _ _ -> p) (noop_t) (fun _ -> acquire l)

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
  intro_lockinv_left p r;
  h_intro_emp_l (lockinv p r);
  h_commute emp (lockinv p r)

let release #p l =
  let r:ref bool = dfst l in
  let i: inv (lockinv p r) = dsnd l in
  let b = lift_atomic_to_steelT (fun _ -> with_invariant_frame i
    (fun _ -> release_core r i))
  in ()

module Steel.SteelAtomic.Basics
open Steel.Effect
open Steel.Effect.Atomic
open Steel.Memory
open Steel.Permissions
module Sem = Steel.Semantics

assume
val return_atomic (#a:Type) (#uses:Set.set lock_addr) (#p:a -> hprop) (x:a)
  : SteelAtomic a uses true (p x) p

val h_admit_atomic (#a:_) (#uses:Set.set lock_addr) (p:hprop) (q:a -> hprop)
  : SteelAtomic a uses true p q
let h_admit_atomic #a #uses p q =
  steel_admit a uses p q

val h_assert_atomic (#uses:Set.set lock_addr) (p:hprop)
  : SteelAtomic unit uses true p (fun _ -> p)
let h_assert_atomic #uses p = steel_assert uses p

val h_intro_emp_l (#uses:Set.set lock_addr) (p:hprop)
  : SteelAtomic unit uses true p (fun _ -> emp `star` p)
let h_intro_emp_l #uses p =
  change_hprop p (emp `star` p) (fun m -> emp_unit p; star_commutative p emp)

val h_elim_emp_l (#uses:Set.set lock_addr) (p:hprop)
  : SteelAtomic unit uses true (emp `star` p) (fun _ -> p)
let h_elim_emp_l #uses p =
  change_hprop (emp `star` p) p (fun m -> emp_unit p; star_commutative p emp)

val h_commute (#uses:Set.set lock_addr) (p q:hprop)
  : SteelAtomic unit uses true (p `star` q) (fun _ -> q `star` p)
let h_commute #uses p q =
   change_hprop (p `star` q) (q `star` p) (fun m -> star_commutative p q)

val h_assoc_left (#uses:Set.set lock_addr) (p q r:hprop)
  : SteelAtomic unit uses true ((p `star` q) `star` r) (fun _ -> p `star` (q `star` r))
let h_assoc_left #uses p q r =
   change_hprop ((p `star` q) `star` r) (p `star` (q `star` r)) (fun m -> star_associative p q r)

val h_assoc_right (#uses:Set.set lock_addr) (p q r:hprop)
  : SteelAtomic unit uses true (p `star` (q `star` r)) (fun _ -> (p `star` q) `star` r)
let h_assoc_right #uses p q r =
   change_hprop (p `star` (q `star` r)) ((p `star` q) `star` r) (fun m -> star_associative p q r)

val intro_h_exists (#a:Type) (#uses:Set.set lock_addr) (x:a) (p:a -> hprop)
  : SteelAtomic unit uses true (p x) (fun _ -> h_exists p)
let intro_h_exists #a #uses x p =
  change_hprop (p x) (h_exists p) (fun m -> intro_exists x p m)

val h_affine (#uses:Set.set lock_addr) (p q:hprop)
  : SteelAtomic unit uses true (p `star` q) (fun _ -> p)
let h_affine #uses p q =
  change_hprop (p `star` q) p (fun m -> affine_star p q m)

val lift_atomic_repr_to_steel_repr
  (#a:Type) (#is_ghost:bool) (#fp:hprop) (#fp':a -> hprop)
  (f:atomic_repr a Set.empty is_ghost fp fp')
  : repr a fp fp' (fun _ -> True) (fun _ _ _ -> True)
let lift_atomic_repr_to_steel_repr #a #is_ghost #fp #fp' f = fun _ -> f ()

val lift_atomic_to_steelT
  (#a:Type) (#is_ghost:bool) (#fp:hprop) (#fp':a -> hprop)
  ($f:unit -> SteelAtomic a Set.empty is_ghost fp fp')
  : SteelT a fp fp'
let lift_atomic_to_steelT #a #is_ghost #fp #fp' f =
  Steel?.reflect (lift_atomic_repr_to_steel_repr (steelatomic_reify f))

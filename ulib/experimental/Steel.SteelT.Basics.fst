module Steel.SteelT.Basics
open Steel.Effect
open Steel.Memory
open Steel.Reference
module AB = Steel.SteelAtomic.Basics

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let return (#a:Type) (#p:a -> hprop) (x:a)
  : SteelT a (p x) p
  = AB.lift_atomic_to_steelT (fun _ -> AB.return_atomic #_ #Set.empty #p x)

let intro_h_exists (#a:Type) (x:a) (p:(a -> hprop))
  : SteelT unit (p x) (fun _ -> h_exists p)
  = AB.lift_atomic_to_steelT (fun _ -> AB.intro_h_exists x p)

let h_assert (p:hprop)
  : SteelT unit p (fun _ -> p)
  = AB.lift_atomic_to_steelT (fun _ -> AB.h_assert_atomic p)

let h_intro_emp_l (p:hprop)
  : SteelT unit p (fun _ -> emp `star` p)
  = AB.lift_atomic_to_steelT (fun _ -> AB.h_intro_emp_l p)

let h_admit (#a:_) (p:hprop) (q:a -> hprop)
  : SteelT a p q
  = AB.lift_atomic_to_steelT (fun _ -> AB.h_admit_atomic p q)

let h_commute (p q:hprop)
  : SteelT unit (p `star` q) (fun _ -> q `star` p)
  = AB.lift_atomic_to_steelT (fun _ -> AB.h_commute p q)

let h_affine (p q:hprop)
  : SteelT unit (p `star` q) (fun _ -> p)
  = AB.lift_atomic_to_steelT (fun _ -> AB.h_affine p q)

let par (#preL:pre_t) (#postL:post_t unit)
        ($f:unit -> SteelT unit preL postL)
        (#preR:pre_t) (#postR:post_t unit)
        ($g:unit -> SteelT unit preR postR)
  : SteelT unit
    (preL `star` preR)
    (fun _ -> postL () `star` postR ())
  = h_admit _ _

let h_elim_emp_l (p:hprop)
  : SteelT unit (emp `star` p) (fun _ -> p)
  = AB.lift_atomic_to_steelT (fun _ -> AB.h_elim_emp_l p)

let frame (#a:Type) (#pre:pre_t) (#post:post_t a)
          ($f:unit -> SteelT a pre post)
          (frame:hprop)
  : SteelT a
    (pre `star` frame)
    (fun x -> post x `star` frame)
  = steel_frame f frame (fun _ -> True)

let noop (#p:hprop) (u:unit) : SteelT unit p (fun _ -> p)
  = return ()

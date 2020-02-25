module Steel.SteelT.Basics
open Steel.Effect
open Steel.Memory
open Steel.Reference


assume
val return (#a:Type) (#p:a -> hprop) (x:a)
  : SteelT a (p x) p

assume
val intro_h_exists (#a:Type) (x:a) (p:(a -> hprop))
  : SteelT unit (p x) (fun _ -> h_exists p)

assume
val h_assert (p:hprop)
  : SteelT unit p (fun _ -> p)

assume
val h_intro_emp_l (p:hprop)
  : SteelT unit p (fun _ -> emp `star` p)

assume
val h_admit (#a:_) (p:hprop) (q:a -> hprop)
  : SteelT a p q

assume
val h_commute (p q:hprop)
  : SteelT unit (p `star` q) (fun _ -> q `star` p)

assume
val h_affine (p q:hprop)
  : SteelT unit (p `star` q) (fun _ -> p)


assume
val par (#preL:pre_t) (#postL:post_t unit)
        ($f:unit -> SteelT unit preL postL)
        (#preR:pre_t) (#postR:post_t unit)
        ($g:unit -> SteelT unit preR postR)
  : SteelT unit
    (preL `star` preR)
    (fun _ -> postL () `star` postR ())

assume
val h_elim_emp_l (p:hprop)
  : SteelT unit (emp `star` p) (fun _ -> p)


assume
val cond (#a:Type) (b:bool) (p: bool -> hprop) (q: bool -> a -> hprop)
         (then_: (unit -> SteelT a (p true) (q true)))
         (else_: (unit -> SteelT a (p false) (q false)))
   : SteelT a (p b) (q b)
//   = if b then (then_ ()) <: SteelT a (p b) (q b) else (else_ () <: SteelT a (p b) (q b))

let frame (#a:Type) (#pre:pre_t) (#post:post_t a)
          ($f:unit -> SteelT a pre post)
          (frame:hprop)
  : SteelT a
    (pre `star` frame)
    (fun x -> post x `star` frame)
  = steel_frame f frame (fun _ -> True)

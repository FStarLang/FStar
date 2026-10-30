module Pulse.Lib.LogicalAtomicity.Locality
#lang-pulse

(** Helpers may exchange placeless abstract state while the AU's captured
client resources and result remain at the initiating caller's locality. *)

open Pulse.Lib.Pervasives
module M = Pulse.Lib.LogicalAtomicity.Masks
module A = Pulse.Lib.LogicalAtomicity.Atomic

private ghost fn prepare_open (#a #b:Type0) l outer inner credits
  (alpha:a -> slprop) (beta phi:a -> b -> slprop)
  requires on l (A.atomic_update outer inner credits alpha beta phi) ** later_credit credits
  ensures on l (A.atomic_update outer inner credits alpha beta phi ** later_credit credits)
{
  placeless_on_intro (later_credit credits) l;
  on_star_intro (A.atomic_update outer inner credits alpha beta phi) (later_credit credits);
}

private ghost fn finish_open (#a #b:Type0) l outer inner credits
  (alpha:a -> slprop) (beta phi:a -> b -> slprop)
  {| pa: (x:a -> placeless (alpha x)) |}
  requires on l (A.opened outer inner alpha
    (A.atomic_update outer inner credits alpha beta phi) beta phi)
  ensures opened l outer inner credits alpha beta phi
{
  rewrite on l (A.opened outer inner alpha
    (A.atomic_update outer inner credits alpha beta phi) beta phi)
    as on l (exists* x. alpha x ** A.closing outer inner alpha
      (A.atomic_update outer inner credits alpha beta phi) beta phi x);
  on_exists_elim (fun x -> alpha x ** A.closing outer inner alpha
    (A.atomic_update outer inner credits alpha beta phi) beta phi x);
  with x. _;
  on_star_elim (alpha x) (A.closing outer inner alpha
    (A.atomic_update outer inner credits alpha beta phi) beta phi x);
  placeless_on_elim (alpha x) #(pa x) l;
  fold opened l outer inner credits alpha beta phi;
}

let open_update (#a #b:Type0) l outer inner credits
  (alpha:a -> slprop) (beta phi:a -> b -> slprop)
  {| pa: (x:a -> placeless (alpha x)) |}
  : M.gaction unit outer inner
      (on l (A.atomic_update outer inner credits alpha beta phi) ** later_credit credits)
      (fun _ -> opened l outer inner credits alpha beta phi) =
  M.bind_ghost (M.lift_ghost outer (prepare_open l outer inner credits alpha beta phi))
    (fun _ ->
      M.bind_ghost (M.localize l (A.open_update outer inner credits alpha beta phi))
        (fun _ -> M.lift_ghost inner (finish_open l outer inner credits alpha beta phi)))

private ghost fn prepare_commit (#a #b:Type0) l outer inner credits
  (alpha:a -> slprop) (beta phi:a -> b -> slprop) x y
  {| pb: placeless (beta x y) |}
  requires on l (A.closing outer inner alpha
    (A.atomic_update outer inner credits alpha beta phi) beta phi x) ** beta x y
  ensures on l (A.closing outer inner alpha
    (A.atomic_update outer inner credits alpha beta phi) beta phi x ** beta x y)
{
  placeless_on_intro (beta x y) l;
  on_star_intro (A.closing outer inner alpha
    (A.atomic_update outer inner credits alpha beta phi) beta phi x) (beta x y);
}

let commit (#a #b:Type0) l outer inner credits
  (alpha:a -> slprop) (beta phi:a -> b -> slprop) x y
  {| pb: placeless (beta x y) |}
  : M.gaction unit inner outer
      (on l (A.closing outer inner alpha
        (A.atomic_update outer inner credits alpha beta phi) beta phi x) ** beta x y)
      (fun _ -> on l (phi x y)) =
  M.bind_ghost (M.lift_ghost inner (prepare_commit l outer inner credits alpha beta phi x y))
    (fun _ -> M.localize l
      (A.commit outer inner alpha (A.atomic_update outer inner credits alpha beta phi) beta phi x y))

private ghost fn prepare_abort (#a #b:Type0) l outer inner credits
  (alpha:a -> slprop) (beta phi:a -> b -> slprop)
  {| pa: (x:a -> placeless (alpha x)) |}
  requires opened l outer inner credits alpha beta phi
  ensures on l (A.opened outer inner alpha
    (A.atomic_update outer inner credits alpha beta phi) beta phi)
{
  unfold opened;
  with x. _;
  placeless_on_intro (alpha x) #(pa x) l;
  on_star_intro (alpha x) (A.closing outer inner alpha
    (A.atomic_update outer inner credits alpha beta phi) beta phi x);
  fold (exists* x. on l (alpha x ** A.closing outer inner alpha
    (A.atomic_update outer inner credits alpha beta phi) beta phi x));
  on_exists_intro (fun x -> alpha x ** A.closing outer inner alpha
    (A.atomic_update outer inner credits alpha beta phi) beta phi x);
  rewrite on l (exists* x. alpha x ** A.closing outer inner alpha
    (A.atomic_update outer inner credits alpha beta phi) beta phi x)
    as on l (A.opened outer inner alpha
      (A.atomic_update outer inner credits alpha beta phi) beta phi);
}

let abort (#a #b:Type0) l outer inner credits
  (alpha:a -> slprop) (beta phi:a -> b -> slprop)
  {| pa: (x:a -> placeless (alpha x)) |}
  : M.gaction unit inner outer (opened l outer inner credits alpha beta phi)
      (fun _ -> on l (A.atomic_update outer inner credits alpha beta phi)) =
  M.bind_ghost (M.lift_ghost inner (prepare_abort l outer inner credits alpha beta phi))
    (fun _ -> M.localize l
      (A.abort_opened outer inner alpha (A.atomic_update outer inner credits alpha beta phi) beta phi))

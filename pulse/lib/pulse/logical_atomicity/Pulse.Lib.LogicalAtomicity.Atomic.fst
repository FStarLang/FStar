module Pulse.Lib.LogicalAtomicity.Atomic
#lang-pulse

open Pulse.Lib.Pervasives
module M = Pulse.Lib.LogicalAtomicity.Masks
module U = Pulse.Lib.LogicalAtomicity.Update

ghost fn intro_closing (#a #b:Type0) (outer inner:inames)
  (alpha:a -> slprop) (abort:slprop) (beta phi:a -> b -> slprop)
  (x:a) (extra:slprop)
  (on_abort:unit -> M.gaction unit inner outer (extra ** alpha x) (fun _ -> abort))
  (on_commit:(y:b -> M.gaction unit inner outer (extra ** beta x y) (fun _ -> phi x y)))
  requires extra
  ensures closing outer inner alpha abort beta phi x
{
  intro_forall # (option b)
    #(fun decision ->
      U.wand inner outer
        (match decision with | None -> alpha x | Some y -> beta x y)
        (match decision with | None -> abort | Some y -> phi x y))
    extra
    fn decision {
      match decision {
        None -> { U.intro_wand inner outer (alpha x) abort extra on_abort; }
        Some y -> { U.intro_wand inner outer (beta x y) (phi x y) extra (fun _ -> on_commit y); }
      }
    };
  fold closing outer inner alpha abort beta phi x;
}

private ghost fn choose (#a #b:Type0) outer inner
  (alpha:a -> slprop) retry (beta phi:a -> b -> slprop) x (decision:option b)
  requires closing outer inner alpha retry beta phi x
  ensures U.wand inner outer
    (match decision with | None -> alpha x | Some y -> beta x y)
    (match decision with | None -> retry | Some y -> phi x y)
{
  unfold closing outer inner alpha retry beta phi x;
  elim_forall decision;
}

let abort #a #b outer inner alpha retry beta phi x =
  M.bind_ghost
    (M.lift_ghost inner (frame_ghost (alpha x) (choose outer inner alpha retry beta phi x None)))
    (fun _ -> U.elim_wand inner outer (alpha x) retry)

let commit #a #b outer inner alpha retry beta phi x y =
  M.bind_ghost
    (M.lift_ghost inner (frame_ghost (beta x y) (choose outer inner alpha retry beta phi x (Some y))))
    (fun _ -> U.elim_wand inner outer (beta x y) (phi x y))

let step_t (#a #b:Type0) outer inner credits (alpha:a -> slprop) (beta phi:a -> b -> slprop) state =
  unit -> M.gaction unit outer inner (state ** later_credit credits)
    (fun _ -> opened outer inner alpha state beta phi)

let step_exists (#a #b:Type0) outer inner credits (alpha:a -> slprop) (beta phi:a -> b -> slprop) state =
  pure (nonempty (step_t outer inner credits alpha beta phi state))

let atomic_update (#a #b:Type0) outer inner credits (alpha:a -> slprop) (beta phi:a -> b -> slprop) =
  exists* state. state ** step_exists outer inner credits alpha beta phi state

ghost fn intro (#a #b:Type0) (outer inner:inames) (credits:nat)
  (alpha:a -> slprop) (beta phi:a -> b -> slprop) (state:slprop)
  (step:unit -> M.gaction unit outer inner (state ** later_credit credits)
    (fun _ -> opened outer inner alpha state beta phi))
  requires state
  ensures atomic_update outer inner credits alpha beta phi
{
  nonempty_intro (step <: step_t outer inner credits alpha beta phi state);
  fold step_exists outer inner credits alpha beta phi state;
  fold atomic_update outer inner credits alpha beta phi;
}

private ghost fn unpack (#a #b:Type0) outer inner credits
  (alpha:a -> slprop) (beta phi:a -> b -> slprop)
  requires atomic_update outer inner credits alpha beta phi
  returns res:(state:erased slprop & step_t outer inner credits alpha beta phi state)
  ensures dfst res
{
  unfold atomic_update outer inner credits alpha beta phi;
  with state. _;
  unfold step_exists outer inner credits alpha beta phi state;
  let step = nonempty_elim (step_t outer inner credits alpha beta phi state);
  (| (state <: erased slprop), step |)
}

private ghost fn restore_update (#a #b:Type0) outer inner credits
  (alpha:a -> slprop) (beta phi:a -> b -> slprop) state
  (step:step_t outer inner credits alpha beta phi state)
  requires opened outer inner alpha state beta phi
  ensures opened outer inner alpha (atomic_update outer inner credits alpha beta phi) beta phi
{
  unfold opened outer inner alpha state beta phi;
  with x. _;
  intro_closing outer inner alpha (atomic_update outer inner credits alpha beta phi) beta phi
    x (closing outer inner alpha state beta phi x)
    (fun _ ->
      M.bind_ghost (abort outer inner alpha state beta phi x)
        (fun _ -> M.lift_ghost outer (intro outer inner credits alpha beta phi state step)))
    (fun y -> commit outer inner alpha state beta phi x y);
  fold opened outer inner alpha (atomic_update outer inner credits alpha beta phi) beta phi;
}

let open_update #a #b outer inner credits alpha beta phi =
  M.bind_ghost
    (M.lift_ghost outer (frame_ghost (later_credit credits) (unpack outer inner credits alpha beta phi)))
    (fun res ->
      M.bind_ghost ((dsnd res) ())
        (fun _ -> M.lift_ghost inner
          (restore_update outer inner credits alpha beta phi (dfst res) (dsnd res))))

private ghost fn unpack_opened (#a #b:Type0) outer inner
  (alpha:a -> slprop) retry (beta phi:a -> b -> slprop)
  requires opened outer inner alpha retry beta phi
  returns x:a
  ensures closing outer inner alpha retry beta phi x ** alpha x
{
  unfold opened outer inner alpha retry beta phi;
  with x. _;
  x
}

let abort_opened #a #b outer inner alpha retry beta phi =
  M.bind_ghost (M.lift_ghost inner (unpack_opened outer inner alpha retry beta phi))
    (fun x -> abort outer inner alpha retry beta phi x)

module Pulse.Lib.LogicalAtomicity.Atomic
#lang-pulse

(**
Owned-state implementation of retryable atomic updates.

The key distinction is between reusable CODE and owned STATE. `step_exists`
is pure, but `atomic_update` owns its existential state. Opening spends
credits and produces one additive closing choice. `restore_update` wraps
the abort path so that restoring state also repackages the same code as an
AU; commit instead consumes the closing resource and returns phi.

This implements the Iris-inspired accessor protocol described in the .fsti
without recursive slprops or additional axioms. The construction provides
no automatic persistence/sendability instance and no progress theorem.
*)

open Pulse.Lib.Pervasives
module M = Pulse.Lib.LogicalAtomicity.Masks
module U = Pulse.Lib.LogicalAtomicity.Update

(** Introduce additive universal quantification over the decision. Each
branch captures the SAME extra resource in a wand, not a copied resource. *)
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

(** Consume the additive choice to obtain exactly the selected wand. *)
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

(** Select None while framing alpha, then run its inner-to-outer wand. *)
let abort #a #b outer inner alpha retry beta phi x =
  M.bind_ghost
    (M.lift_ghost inner (frame_ghost (alpha x) (choose outer inner alpha retry beta phi x None)))
    (fun _ -> U.elim_wand inner outer (alpha x) retry)

(** Select Some y while framing beta; the other closing branch is lost. *)
let commit #a #b outer inner alpha retry beta phi x y =
  M.bind_ghost
    (M.lift_ghost inner (frame_ghost (beta x y) (choose outer inner alpha retry beta phi x (Some y))))
    (fun _ -> U.elim_wand inner outer (beta x y) (phi x y))

(** The retry invariant's code type: an opening returns an accessor that can
abort back to the same state, after consuming this attempt's credits. *)
let step_t (#a #b:Type0) outer inner credits (alpha:a -> slprop) (beta phi:a -> b -> slprop) state =
  unit -> M.gaction unit outer inner (state ** later_credit credits)
    (fun _ -> opened outer inner alpha state beta phi)

(** Pure availability of a step witness; this does not assert state ownership. *)
let step_exists (#a #b:Type0) outer inner credits (alpha:a -> slprop) (beta phi:a -> b -> slprop) state =
  pure (nonempty (step_t outer inner credits alpha beta phi state))

(** Existential package of the retry invariant and its owned current state. *)
let atomic_update (#a #b:Type0) outer inner credits (alpha:a -> slprop) (beta phi:a -> b -> slprop) =
  exists* state. state ** step_exists outer inner credits alpha beta phi state

(** Hide the selected retry invariant and establish its code witness. *)
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

(** Recover the existential state and matching step, consuming the AU package. *)
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

(** Strengthen a raw accessor's abort result from hidden state to a fresh AU
package. The original commit branch is forwarded unchanged. This is the
coinduction-style step that makes later retries possible, not a credit refund. *)
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

(** Unpack, spend credits through the step, then install the self-restoring
abort branch. All three pieces are ghost-only mask transitions. *)
let open_update #a #b outer inner credits alpha beta phi =
  M.bind_ghost
    (M.lift_ghost outer (frame_ghost (later_credit credits) (unpack outer inner credits alpha beta phi)))
    (fun res ->
      M.bind_ghost ((dsnd res) ())
        (fun _ -> M.lift_ghost inner
          (restore_update outer inner credits alpha beta phi (dfst res) (dsnd res))))

(** Expose the attempt's abstract-state witness with its alpha and closer. *)
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

(** Forget the particular abstract-state witness by immediately aborting. *)
let abort_opened #a #b outer inner alpha retry beta phi =
  M.bind_ghost (M.lift_ghost inner (unpack_opened outer inner alpha retry beta phi))
    (fun x -> abort outer inner alpha retry beta phi x)

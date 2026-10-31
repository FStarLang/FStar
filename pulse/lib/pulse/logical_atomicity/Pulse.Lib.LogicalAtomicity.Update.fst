module Pulse.Lib.LogicalAtomicity.Update
#lang-pulse

(**
Representation and proofs for the update-wand interface.

A wand is an existential resource package: hidden `extra` ownership plus
pure evidence that a suitable ghost runner exists. Keeping code existence
pure does NOT make its captured resources duplicable. This representation
supports resource-capturing client continuations without axioms about a new
modal connective. All execution is delegated to the verified Masks layer.
The public .fsti gives the Iris analogy and the limits of that analogy.
*)

open Pulse.Lib.Pervasives
module M = Pulse.Lib.LogicalAtomicity.Masks

(** Code that consumes captured state and input at the initial mask. The
unit thunk delays construction/execution until the package is eliminated. *)
let runner before after p q extra =
  unit -> M.gaction unit before after (extra ** p) (fun _ -> q)

(** Pure evidence of code availability, separate from ownership of `extra`.
`nonempty` avoids storing an executable function inside a spatial assertion. *)
let runner_exists before after p q extra =
  pure (nonempty (runner before after p q extra))

(** Hide captured ownership and its matching runner together. The witness
may be reused as code, but each invocation still needs the hidden resource. *)
let wand (before after:inames) (p q:slprop) =
  exists* extra. extra ** runner_exists before after p q extra

(** Establish code existence and existentially hide the owned environment. *)
ghost fn intro_wand (before after:inames) (p q extra:slprop)
  (k:unit -> M.gaction unit before after (extra ** p) (fun _ -> q))
  requires extra
  ensures wand before after p q
{
  nonempty_intro (k <: runner before after p q extra);
  fold runner_exists before after p q extra;
  fold wand before after p q;
}

(** Recover a matching runner and its erased resource index. The postcondition
returns the resource itself, not just knowledge that it exists. *)
private ghost fn unpack (before after:inames) (p q:slprop)
  requires wand before after p q
  returns res:(extra:erased slprop & runner before after p q extra)
  ensures dfst res
{
  unfold wand before after p q;
  with extra. _;
  unfold runner_exists before after p q extra;
  let k = nonempty_elim (runner before after p q extra);
  (| (extra <: erased slprop), k |)
}

(** Unpack while framing the supplied input, then invoke the recovered code.
Mask changes occur in the runner, not in unpacking. *)
let elim_wand before after p q
  : M.gaction unit before after (wand before after p q ** p) (fun _ -> q) =
  M.bind_ghost
    (M.lift_ghost before (Pulse.Lib.Core.frame_ghost p (unpack before after p q)))
    (fun res -> (dsnd res) ())

(** Capture `p` in an identity runner with empty additional input. *)
ghost fn return_update (mask:inames) (p:slprop)
  requires p
  ensures fupd mask mask p
{
  ghost fn identity () requires p ** emp ensures p {};
  star_comm p emp;
  emp_unit p;
  intro_wand mask mask emp p p (fun _ -> M.lift_ghost mask (identity ()));
  fold fupd mask mask p;
}

(** Discharge the empty input using separation's unit law. *)
let elim_update before after p
  : M.gaction unit before after (fupd before after p) (fun _ -> p) =
  star_comm (fupd before after p) emp;
  emp_unit (fupd before after p);
  elim_wand before after emp p

(** Capture both hidden environments; frame the second across the first
runner, then feed the first result to the second. *)
ghost fn compose (m1 m2 m3:inames) (p q r:slprop)
  requires wand m1 m2 p q ** wand m2 m3 q r
  ensures wand m1 m3 p r
{
  let f = unpack m1 m2 p q;
  let g = unpack m2 m3 q r;
  slprop_equivs ();
  rewrite each dfst f as f._1;
  rewrite each dfst g as g._1;
  intro_wand m1 m3 p r (dfst f ** dfst g) (fun _ ->
    star_assoc (dfst f) (dfst g) p;
    star_comm (dfst g) p;
    M.bind_ghost
      (M.frame_ghost (dfst g) ((dsnd f) ()))
      (fun _ ->
        star_comm q (dfst g);
        (dsnd g) ()));
}

(** Repackage the original environment with a runner that frames `r`. *)
ghost fn frame (m1 m2:inames) (p q r:slprop)
  requires wand m1 m2 p q
  ensures wand m1 m2 (p ** r) (q ** r)
{
  let f = unpack m1 m2 p q;
  slprop_equivs ();
  rewrite each dfst f as f._1;
  intro_wand m1 m2 (p ** r) (q ** r) (dfst f) (fun _ ->
    star_assoc (dfst f) p r;
    M.frame_ghost r ((dsnd f) ()));
}

(** Package the postprocessing computation with an empty environment and
compose it after the original emp-input wand. *)
ghost fn map (m1 m2:inames) (p q:slprop)
  (k:unit -> stt_ghost unit emp_inames p (fun _ -> q))
  requires fupd m1 m2 p
  ensures fupd m1 m2 q
{
  unfold fupd m1 m2 p;
  emp_unit p;
  intro_wand m2 m2 p q emp (fun _ ->
    M.lift_ghost m2 (k ()));
  compose m1 m2 m2 emp p q;
  fold fupd m1 m2 q;
}

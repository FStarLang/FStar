(* `inspect_pack_comp_inv` in ulib/FStar.Stubs.Reflection.V2.Builtins.fsti is
   *assumed*, and both `inspect_comp` and `pack_comp` are registered primitive
   normalizer steps, so any view that is not in the image of `inspect_comp` lets
   the normalizer contradict the axiom and prove False.  This test checks the
   round trip by computation for the views the axiom covers, and pins down what
   happens to the one it does not (a `C_Eff` naming `FStar.Pervasives.Lemma`). *)
module CompRoundTrip

open FStar.Tactics.V2
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Stubs.Reflection.V2.Data

let res : term = pack_ln (Tv_Const C_Unit)
let tt : term = pack_ln (Tv_Const C_True)

let check () : Tac unit =
  norm [primops; delta; iota; zeta];
  trefl ()

let cv_eff : comp_view = C_Eff [] ["CompRoundTrip"; "M"] res tt tt []

let eff_round_trips () : Lemma (inspect_comp (pack_comp cv_eff) == cv_eff) =
  assert (inspect_comp (pack_comp cv_eff) == cv_eff) by check ()

let cv_eff_decrs : comp_view = C_Eff [] ["CompRoundTrip"; "M"] res tt tt [res]

let eff_decrs_round_trips ()
  : Lemma (inspect_comp (pack_comp cv_eff_decrs) == cv_eff_decrs) =
  assert (inspect_comp (pack_comp cv_eff_decrs) == cv_eff_decrs) by check ()

let cv_total : comp_view = C_Total res

let total_round_trips () : Lemma (inspect_comp (pack_comp cv_total) == cv_total) =
  assert (inspect_comp (pack_comp cv_total) == cv_total) by check ()

let cv_ghost : comp_view = C_GTotal res

let ghost_round_trips () : Lemma (inspect_comp (pack_comp cv_ghost) == cv_ghost) =
  assert (inspect_comp (pack_comp cv_ghost) == cv_ghost) by check ()

let cv_lemma : comp_view = C_Lemma tt tt tt

let lemma_round_trips () : Lemma (inspect_comp (pack_comp cv_lemma) == cv_lemma) =
  assert (inspect_comp (pack_comp cv_lemma) == cv_lemma) by check ()

(* The one view outside the image of `inspect_comp`: naming `FStar.Pervasives.Lemma` in a
   `C_Eff` comes back as a `C_Lemma`, which is why `inspect_pack_comp_inv`
   excludes it. *)

let cv_eff_lemma : comp_view = C_Eff [] ["FStar"; "Pervasives"; "Lemma"] res tt tt []

let eff_lemma_does_not_round_trip ()
  : Lemma (C_Lemma? (inspect_comp (pack_comp cv_eff_lemma)))
  = assert (C_Lemma? (inspect_comp (pack_comp cv_eff_lemma)))
        by (norm [primops; delta; iota; zeta]; trivial ())

(* ... and so the axiom may not be instantiated at it. *)

[@@expect_failure [19]]
let eff_lemma_inv_rejected () : Lemma (inspect_comp (pack_comp cv_eff_lemma) == cv_eff_lemma) =
  inspect_pack_comp_inv cv_eff_lemma

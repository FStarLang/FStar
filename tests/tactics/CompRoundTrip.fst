(* `inspect_comp` and `pack_comp` must be mutual inverses on views: the axiom

       val inspect_pack_comp_inv : (cv:comp_view) ->
             Lemma (inspect_comp (pack_comp cv) == cv)

   in ulib/FStar.Stubs.Reflection.V2.Builtins.fsti is *assumed*, and both
   functions are registered primitive normalizer steps, so any view that is not
   in the image of `inspect_comp` lets the normalizer contradict the axiom and
   prove False.  This test checks the round trip by computation. *)
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

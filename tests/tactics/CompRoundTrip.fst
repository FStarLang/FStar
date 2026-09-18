(* `inspect_pack_comp_inv` and `pack_inspect_comp_inv` in
   ulib/FStar.Stubs.Reflection.V2.Builtins.fsti are *assumed*, and both
   `inspect_comp` and `pack_comp` are registered primitive normalizer steps, so
   any view that is not in the image of `inspect_comp` would let the normalizer
   contradict an axiom and prove False.  `comp_view` is now a record mirroring
   `comp_typ` field for field, so `inspect_comp` is a bijection and both
   directions hold unconditionally; this test checks a representative sample by
   computation. *)
module CompRoundTrip

open FStar.Tactics.V2
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Stubs.Reflection.V2.Data

let res : term = pack_ln (Tv_Const C_Unit)
let tt : term = pack_ln (Tv_Const C_True)

let check () : Tac unit =
  norm [primops; delta; iota; zeta];
  trefl ()

let cv_total : comp_view = mk_tot_comp res

let total_round_trips () : Lemma (inspect_comp (pack_comp cv_total) == cv_total) =
  assert (inspect_comp (pack_comp cv_total) == cv_total) by check ()

let cv_ghost : comp_view = mk_gtot_comp res

let ghost_round_trips () : Lemma (inspect_comp (pack_comp cv_ghost) == cv_ghost) =
  assert (inspect_comp (pack_comp cv_ghost) == cv_ghost) by check ()

(* An arbitrary effect name, which is no longer a special case. *)

let cv_eff : comp_view = mk_comp_view ["CompRoundTrip"; "M"] res

let eff_round_trips () : Lemma (inspect_comp (pack_comp cv_eff) == cv_eff) =
  assert (inspect_comp (pack_comp cv_eff) == cv_eff) by check ()

(* `source_effect_name` records the abbreviation the user wrote; it is preserved
   independently of `effect_name`. *)

let cv_lemma : comp_view = {
  effect_name = tot_effect_name;
  result_typ = res;
  flags = [];
  source_effect_name = ["FStar"; "Pervasives"; "Lemma"];
}

let lemma_round_trips () : Lemma (inspect_comp (pack_comp cv_lemma) == cv_lemma) =
  assert (inspect_comp (pack_comp cv_lemma) == cv_lemma) by check ()

(* Flags round trip too, including both shapes of decreases clause. *)

let cv_flags : comp_view = {
  effect_name = tot_effect_name;
  result_typ = res;
  flags = [SMTPAT tt; DECREASES (Decreases_lex [res; tt]); DECREASES (Decreases_wf res tt)];
  source_effect_name = tot_effect_name;
}

let flags_round_trip () : Lemma (inspect_comp (pack_comp cv_flags) == cv_flags) =
  assert (inspect_comp (pack_comp cv_flags) == cv_flags) by check ()

(* ... and the axiom covers all of them, with no side condition. *)

let inv_accepted (cv : comp_view) : Lemma (inspect_comp (pack_comp cv) == cv) =
  inspect_pack_comp_inv cv

let inv_accepted' (c : FStar.Stubs.Reflection.Types.comp) : Lemma (pack_comp (inspect_comp c) == c) =
  pack_inspect_comp_inv c

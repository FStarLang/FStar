(* `inspect_pack_comp_inv` in ulib/FStar.Stubs.Reflection.V2.Builtins.fsti is
   *assumed*, and both `inspect_comp` and `pack_comp` are registered primitive
   normalizer steps, so any view that is not in the image of `inspect_comp` lets
   the normalizer contradict the axiom and prove False.  `comp_view` is strictly
   richer than `comp`, so only `C_Total` and `C_GTotal` round trip; this test
   checks those two by computation, and pins down what happens to each of the
   views the axiom does not cover. *)
module CompRoundTrip

open FStar.Tactics.V2
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Stubs.Reflection.V2.Data

let res : term = pack_ln (Tv_Const C_Unit)
let tt : term = pack_ln (Tv_Const C_True)

let check () : Tac unit =
  norm [primops; delta; iota; zeta];
  trefl ()

let cv_total : comp_view = C_Total res

let total_round_trips () : Lemma (inspect_comp (pack_comp cv_total) == cv_total) =
  assert (inspect_comp (pack_comp cv_total) == cv_total) by check ()

let cv_ghost : comp_view = C_GTotal res

let ghost_round_trips () : Lemma (inspect_comp (pack_comp cv_ghost) == cv_ghost) =
  assert (inspect_comp (pack_comp cv_ghost) == cv_ghost) by check ()

(* ... and the axiom applies to exactly those two. *)

let total_inv_accepted () : Lemma (inspect_comp (pack_comp cv_total) == cv_total) =
  inspect_pack_comp_inv cv_total

let ghost_inv_accepted () : Lemma (inspect_comp (pack_comp cv_ghost) == cv_ghost) =
  inspect_pack_comp_inv cv_ghost

(* Everything below is outside the image of `inspect_comp`.  Each of these was
   once permitted by the axiom's precondition, and each of them proves False. *)

(* 1. A `C_Eff` naming `Prims.Tot` (or `Prims.GTot`) with no decreases clause:
      `inspect_comp` canonicalizes the constructor, so the view comes back as a
      `C_Total` (resp. `C_GTotal`). *)

let cv_eff_tot : comp_view = C_Eff [] ["Prims"; "Tot"] res tt tt []

let eff_tot_does_not_round_trip ()
  : Lemma (C_Total? (inspect_comp (pack_comp cv_eff_tot)))
  = assert (C_Total? (inspect_comp (pack_comp cv_eff_tot)))
        by (norm [primops; delta; iota; zeta]; trivial ())

[@@expect_failure [19]]
let eff_tot_inv_rejected () : Lemma (inspect_comp (pack_comp cv_eff_tot) == cv_eff_tot) =
  inspect_pack_comp_inv cv_eff_tot

let cv_eff_gtot : comp_view = C_Eff [] ["Prims"; "GTot"] res tt tt []

let eff_gtot_does_not_round_trip ()
  : Lemma (C_GTotal? (inspect_comp (pack_comp cv_eff_gtot)))
  = assert (C_GTotal? (inspect_comp (pack_comp cv_eff_gtot)))
        by (norm [primops; delta; iota; zeta]; trivial ())

[@@expect_failure [19]]
let eff_gtot_inv_rejected () : Lemma (inspect_comp (pack_comp cv_eff_gtot) == cv_eff_gtot) =
  inspect_pack_comp_inv cv_eff_gtot

(* 2. A `C_Eff` naming `FStar.Pervasives.Lemma` always comes back as a
      `C_Lemma`. *)

let cv_eff_lemma : comp_view = C_Eff [] ["FStar"; "Pervasives"; "Lemma"] res tt tt []

let eff_lemma_does_not_round_trip ()
  : Lemma (C_Lemma? (inspect_comp (pack_comp cv_eff_lemma)))
  = assert (C_Lemma? (inspect_comp (pack_comp cv_eff_lemma)))
        by (norm [primops; delta; iota; zeta]; trivial ())

[@@expect_failure [19]]
let eff_lemma_inv_rejected () : Lemma (inspect_comp (pack_comp cv_eff_lemma) == cv_eff_lemma) =
  inspect_pack_comp_inv cv_eff_lemma

(* 3. A computation type stores no universes -- an effect is applied to its
      result type alone, so its universe is that type's -- and `pack_comp`
      drops them. *)

let cv_eff_us : comp_view = C_Eff [pack_universe Uv_Zero] ["CompRoundTrip"; "M"] res tt tt []

[@@expect_failure [19]]
let eff_us_inv_rejected () : Lemma (inspect_comp (pack_comp cv_eff_us) == cv_eff_us) =
  inspect_pack_comp_inv cv_eff_us

(* 4. A computation type carries no specification: a `C_Eff`'s precondition is
      dropped outright (it is a binder on the arrow, out of reach here) and its
      postcondition is only ever the one read back off the result type.  Both
      come back canonicalized, whatever the view supplied. *)

let cv_eff : comp_view = C_Eff [] ["CompRoundTrip"; "M"] res tt tt []

[@@expect_failure [19]]
let eff_inv_rejected () : Lemma (inspect_comp (pack_comp cv_eff) == cv_eff) =
  inspect_pack_comp_inv cv_eff

(* 5. The same holds of a `C_Lemma`'s precondition. *)

let cv_lemma : comp_view = C_Lemma tt tt tt

[@@expect_failure [19]]
let lemma_inv_rejected () : Lemma (inspect_comp (pack_comp cv_lemma) == cv_lemma) =
  inspect_pack_comp_inv cv_lemma

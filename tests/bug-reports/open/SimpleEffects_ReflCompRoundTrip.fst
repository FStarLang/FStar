(*
   `inspect_comp` and `pack_comp` must be mutual inverses on views: the
   *trusted, unproven* axiom

       val inspect_pack_comp_inv : (cv:comp_view) ->
             Lemma (inspect_comp (pack_comp cv) == cv)

   in ulib/FStar.Stubs.Reflection.V2.Builtins.fsti is quantified over ALL
   `comp_view`s, and `C_Eff` carries an unconstrained `eff_args : list argv`.

   On the `gebner_simple_effects` branch,
   src/reflection/FStarC.Reflection.V2.Builtins.fst makes `inspect_comp` always
   synthesize exactly two explicit args for a non-Lemma `C_Eff`

       [(ct.comp_pre, Q_Explicit); (ct.comp_post, Q_Explicit)]

   while `pack_comp` reads only the first two and silently discards the rest,
   the aquals and the arity.  Both are registered primitive normalizer steps, so
   the normalizer computes the real result and contradicts the axiom for any
   `C_Eff` view whose arg list is not exactly two explicit args -- proving
   False.  (A `C_Eff` view naming the `Lemma` lid is a second round-trip
   violation: it comes back as `C_Lemma`.)

   The assertion below MUST fail.  When fixed, move to tests/tactics/ alongside
   the other inspect/pack round-trip tests.
*)
module SimpleEffects_ReflCompRoundTrip

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Data
open FStar.Stubs.Reflection.V2.Builtins

let res : term = pack_ln (Tv_Const C_Unit)

/// `eff_args = []`: `pack_comp` invents a (pre, post) pair, and `inspect_comp`
/// hands back two args, so the round trip is not the identity.
let cv_empty : comp_view = C_Eff [] ["SimpleEffects_ReflCompRoundTrip"; "M"] res [] []

[@@ expect_failure]
let round_trip_is_false () : Lemma False =
  inspect_pack_comp_inv cv_empty;
  assert (Cons? (C_Eff?.eff_args (inspect_comp (pack_comp cv_empty))))
      by (FStar.Tactics.norm [primops; delta; iota; zeta]; FStar.Tactics.trefl ())

/// A `C_Eff` view carrying more than two args loses the extra ones.
let cv_three : comp_view =
  C_Eff [] ["SimpleEffects_ReflCompRoundTrip"; "M"] res
        [(res, Q_Explicit); (res, Q_Explicit); (res, Q_Explicit)] []

[@@ expect_failure]
let extra_args_dropped () : Lemma False =
  inspect_pack_comp_inv cv_three;
  assert (cv_three == inspect_comp (pack_comp cv_three))
      by (FStar.Tactics.norm [primops; delta; iota; zeta]; FStar.Tactics.trefl ())

/// The round trip that DOES hold must keep holding.
let cv_total : comp_view = C_Total res

let total_round_trips () : Lemma (inspect_comp (pack_comp cv_total) == cv_total) =
  inspect_pack_comp_inv cv_total

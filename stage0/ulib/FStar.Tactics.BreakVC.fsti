module FStar.Tactics.BreakVC

open FStar.Tactics
open FStar.Stubs.Tactics.Result

let break_wp' : tac_wp_t0 unit =
  fun ps p -> spinoff (squash (p (Success () ps)))

val mono_lem () : Lemma (tac_wp_monotonic #unit break_wp')

private
let post () : Tac unit =
  norm [delta_fully [`%mono_lem; `%break_wp']];
  trefl()

[@@postprocess_with post]
unfold
let break_wp : tac_wp_t unit =
  let _ = mono_lem () in
  break_wp'

val break_vc () : TAC unit break_wp

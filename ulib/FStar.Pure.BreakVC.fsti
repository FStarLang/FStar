module FStar.Pure.BreakVC

open FStar.Tactics

let break_wp' : pure_wp' unit =
  fun p -> spinoff (squash (p ()))

val mono_lem () : Lemma (pure_wp_monotonic unit break_wp')

private
let post () : Tac unit =
  norm [delta_fully [`%mono_lem; `%break_wp']];
  trefl()

[@@postprocess_with post]
unfold
let break_wp : pure_wp unit =
  let _ = mono_lem () in
  break_wp'

val break_vc () : PURE unit break_wp

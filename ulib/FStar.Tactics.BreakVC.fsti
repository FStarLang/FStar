module FStar.Tactics.BreakVC

open FStar.Tactics

(* See FStar.Pure.BreakVC: VC-breaking cannot be expressed with pre- and
   postconditions alone, so this is a no-op kept for source compatibility. *)
val break_vc (_:unit) : Tac unit

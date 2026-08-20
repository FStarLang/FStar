module OvlGhostA
open FStar.Ghost

(* A candidate whose formal is an [erased int]: an [int] argument reaches it
   only because the elaborator inserts [hide]. *)
let h (x : erased int) : int = 0

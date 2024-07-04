open Prims
let (canon_slprop : Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term) =
  fun vp ->
    Pulse_Syntax_Pure.list_as_slprop (Pulse_Syntax_Pure.slprop_as_list vp)


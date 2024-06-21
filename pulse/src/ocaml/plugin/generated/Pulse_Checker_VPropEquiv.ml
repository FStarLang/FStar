open Prims
let (canon_vprop : Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term) =
  fun vp ->
    Pulse_Syntax_Pure.list_as_vprop (Pulse_Syntax_Pure.vprop_as_list vp)


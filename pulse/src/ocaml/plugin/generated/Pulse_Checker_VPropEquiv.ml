open Prims
let (canon_vprop : Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term) =
  fun vp ->
    Pulse_Typing_Combinators.list_as_vprop
      (Pulse_Typing_Combinators.vprop_as_list vp)


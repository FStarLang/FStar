module Pulse.Readback
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open Pulse.Syntax
open Pulse.Elaborate.Pure

val readback_universe (u:R.universe)
  : o:option universe{ Some? o ==> elab_universe (Some?.v o) == u }

val readback_universes (us:list R.universe)
  : o:option (list universe) { 
          Some? o ==> L.map elab_universe (Some?.v o) == us 
    }

val readback_qual (q:R.aqualv)
  : option qualifier
  
val readback_ty (t:R.term)
  : T.Tac (option (ty:pure_term { elab_term ty == Some t }))

val readback_comp (t:R.term)
  : T.Tac (option (c:comp{ elab_comp c == Some t}))


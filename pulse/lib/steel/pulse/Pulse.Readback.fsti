module Pulse.Readback
module R = FStar.Reflection
module L = FStar.List.Tot
open Pulse.Syntax.Base
open Pulse.Elaborate.Pure

val readback_qual (q:R.aqualv)
  : option qualifier
  
val readback_ty (t:R.term)
  : option (ty:term { elab_term ty == t })

val readback_comp (t:R.term)
  : option (c:comp{ elab_comp c == t})

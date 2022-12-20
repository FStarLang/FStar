module Refl.Typing.Builtins
open FStar.Reflection

val dummy_range : range

val open_with (t:term) (v:term) : term
  
val open_term (t:term) (v:var) : term

val close_term (t:term) (v:var) : term

val rename (t:term) (x y:var) : term

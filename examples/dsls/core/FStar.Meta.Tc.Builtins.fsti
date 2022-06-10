module FStar.Meta.Tc.Builtins

open FStar.Reflection.Types
open FStar.Meta.Tc.Effect

val valid_prop (en:env) (t:typ) : Type0

val check_prop_validity (en:env) (t:typ) : MetaTcT (valid_prop en t)

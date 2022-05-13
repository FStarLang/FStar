module FStar.Meta.Tc.Builtins

open FStar.Reflection.Types
open FStar.Meta.Tc.Effect

val tc_term (en:env) (t:term) : MetaTcT term

module FStar.Reflection.Types

assume new type binder
assume new type bv
assume new type term
assume new type env
assume new type fv
assume new type comp
assume new type sigelt
assume new type ctx_uvar_and_subst
assume new type ident

type name : eqtype = list string
type univ_name = range * string
type typ     = term
type binders = list binder

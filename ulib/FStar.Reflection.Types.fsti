module FStar.Reflection.Types

assume new type binder
assume new type bv
assume new type term
assume new type env
assume new type fv
assume new type comp
assume new type sigelt // called `def` in the paper, but we keep the internal name here
assume new type ctx_uvar_and_subst

type name : eqtype = list string
type ident = range * string
type univ_name = ident
type typ     = term
type binders = list binder

open Prims
type binder = FStar_Syntax_Syntax.binder
type term = FStar_Syntax_Syntax.term
type env = FStar_TypeChecker_Env.env
type fv = FStar_Syntax_Syntax.fv

type typ = term
type name = Prims.string list
type binders = binder list

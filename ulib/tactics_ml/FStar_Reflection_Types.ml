open FStar_All

type binder=FStar_Syntax_Syntax.binder
type term=FStar_Syntax_Syntax.term
type env=FStar_TypeChecker_Env.env
type fv=FStar_Syntax_Syntax.fv
type comp=FStar_Syntax_Syntax.comp

type typ = term
type name = string list
type binders = binder list

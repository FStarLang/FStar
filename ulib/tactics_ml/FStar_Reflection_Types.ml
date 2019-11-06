open FStar_All

type binder  = FStar_Syntax_Syntax.binder
type bv      = FStar_Syntax_Syntax.bv
type term    = FStar_Syntax_Syntax.term
type env     = FStar_TypeChecker_Env.env
type fv      = FStar_Syntax_Syntax.fv
type comp    = FStar_Syntax_Syntax.comp
type sigelt  = FStar_Syntax_Syntax.sigelt
type ctx_uvar_and_subst = FStar_Syntax_Syntax.ctx_uvar_and_subst
type optionstate = FStar_Options.optionstate

type name        = string list
type ident       = FStar_Range.range * string
type univ_name   = ident
type typ         = term
type binders     = binder list

(* TODO: make this an F* module, no need to drop to OCaml for this *)

(* Used externally. *)

type binder  = FStarC_Syntax_Syntax.binder
type bv      = FStarC_Syntax_Syntax.bv
type namedv  = bv
type term    = FStarC_Syntax_Syntax.term
type env     = FStarC_TypeChecker_Env.env
type fv      = FStarC_Syntax_Syntax.fv
type comp    = FStarC_Syntax_Syntax.comp
type sigelt  = FStarC_Syntax_Syntax.sigelt
type ctx_uvar_and_subst = FStarC_Syntax_Syntax.ctx_uvar_and_subst
type optionstate = FStarC_Options.optionstate
type letbinding = FStarC_Syntax_Syntax.letbinding

type universe_uvar = FStarC_Syntax_Syntax.universe_uvar
type universe = FStarC_Syntax_Syntax.universe

type name        = string list
type ident       = FStarC_Ident.ident
type univ_name   = ident
type typ         = term
type binders     = binder list
type match_returns_ascription = FStarC_Syntax_Syntax.match_returns_ascription
type decls = sigelt list

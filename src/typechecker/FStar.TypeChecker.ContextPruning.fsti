module FStar.TypeChecker.ContextPruning
open FStar.Syntax.Syntax
open FStar.TypeChecker.Env
open FStar.Ident
val context_of (env:env) (t:list term) : list lident
module FStar.Tactics.Interpreter

open FStar.Syntax.Syntax
open FStar.TypeChecker.Env

val preprocess: env -> term -> list<(env * term)>

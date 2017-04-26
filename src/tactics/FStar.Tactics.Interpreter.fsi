#light "off"
module FStar.Tactics.Interpreter
open FStar
open FStar.All
open FStar.Syntax.Syntax

val preprocess: FStar.TypeChecker.Env.env -> term -> list<(FStar.TypeChecker.Env.env * term)>

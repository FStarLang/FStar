#light "off"
module FStar.Tactics.Interpreter

open FStar.Syntax.Syntax
module Env = FStar.TypeChecker.Env

val preprocess: Env.env -> term -> list<(Env.env * term)>

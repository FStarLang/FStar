#light "off"
module FStar.Tactics.Hooks

open FStar.Syntax.Syntax
open FStar.Compiler.Range

module O   = FStar.Options
module Env = FStar.TypeChecker.Env

val preprocess      : Env.env -> term -> list<(Env.env * term * O.optionstate)>
val handle_smt_goal : Env.env -> Env.goal -> list<(Env.env * term)>
val synthesize      : Env.env -> typ -> term -> term
val solve_implicits : Env.env -> term -> Env.implicits -> unit
val splice          : Env.env -> range -> term -> list<sigelt>
val mpreprocess     : Env.env -> term -> term -> term
val postprocess     : Env.env -> term -> typ -> term -> term

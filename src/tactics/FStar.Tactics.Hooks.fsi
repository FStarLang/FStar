#light "off"
module FStar.Tactics.Hooks

open FStar.Syntax.Syntax

module O   = FStar.Options
module Env = FStar.TypeChecker.Env

val preprocess: Env.env -> term -> list<(Env.env * term * O.optionstate)>
val synthesize: Env.env -> typ -> term -> term
val solve_implicits: Env.env -> term -> Env.implicits -> unit
val splice : Env.env -> Range.range -> term -> list<sigelt>
val mpreprocess : Env.env -> term -> term -> term
val postprocess : Env.env -> term -> typ -> term -> term

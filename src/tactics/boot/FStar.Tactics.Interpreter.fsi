#light "off"
module FStar.Tactics.Interpreter
open FStar
open FStar.ST
open FStar.All
open FStar.Syntax.Syntax
module Env = FStar.TypeChecker.Env

val preprocess: Env.env -> term -> list<(Env.env * term * FStar.Options.optionstate)>
val synthesize: Env.env -> typ -> term -> term
val splice : Env.env -> term -> list<sigelt>

val primitive_steps : unit -> list<FStar.TypeChecker.Cfg.primitive_step>

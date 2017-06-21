#light "off"
module FStar.Tactics.Interpreter
open FStar
open FStar.ST
open FStar.All
open FStar.Syntax.Syntax
module Env = FStar.TypeChecker.Env

val preprocess: Env.env -> term -> list<(Env.env * term * FStar.Options.optionstate)>
val synth: Env.env -> typ -> term -> term

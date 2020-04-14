#light "off"
module FStar.Tactics.Interpreter

open FStar.ST
open FStar.Range
open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
open FStar.Tactics.Types
module Env = FStar.TypeChecker.Env

val run_tactic_on_ps :
    range -> (* position on the tactic *)
    range -> (* position for the goal *)
    embedding<'a> ->
    'a ->
    embedding<'b> ->
    term ->        (* a term representing an `'a -> tac 'b` *)
    proofstate ->  (* proofstate *)
    list<goal> * 'b (* goals and return value *)

val primitive_steps : unit -> list<FStar.TypeChecker.Cfg.primitive_step>

val report_implicits : range -> Env.implicits -> unit

(* For debugging only *)
val tacdbg : ref<bool>

module FStar.SMTEncoding.Pruning
open FStar.Compiler.Effect
open FStar
open FStar.Compiler
open FStar.SMTEncoding.Term

val pruning_state  : Type0

val init : pruning_state
val add_assumptions (ds:list decl) (p:pruning_state) : pruning_state
val prune (p:pruning_state) (roots:list decl) : list decl
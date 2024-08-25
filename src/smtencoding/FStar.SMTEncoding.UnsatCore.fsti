module FStar.SMTEncoding.UnsatCore
open FStar.Compiler.Effect
open FStar
open FStar.Compiler
open FStar.SMTEncoding.Term

type unsat_core = list string

val filter (s:unsat_core) (decls:list decl)
: list decl
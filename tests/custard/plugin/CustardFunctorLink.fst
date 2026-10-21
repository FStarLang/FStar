module CustardFunctorLink

(* Issue #4689.  A --with_fstarc unit that re-specializes compiler code
   touching a [FStarC.HashTable].  See the Makefile. *)

open FStarC
open FStarC.Effect
module DsEnv = FStarC.Syntax.DsEnv

(* Not reached from the compiler's own roots, so this unit compiles it
   itself, and its body uses the compiler's [string] hash table. *)
let exported (env:DsEnv.env) (l:Ident.lident) : ML (list string) =
  DsEnv.transitive_exported_ids env l

let _ = FStarC.Format.print_string "CustardFunctorLink: loaded\n"

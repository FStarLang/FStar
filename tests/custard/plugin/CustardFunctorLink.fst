module CustardFunctorLink

(* Issue #4689.  A --with_fstarc unit that re-specializes compiler code
   touching a [FStarC.HashTable].  See the Makefile. *)

open FStarC
open FStarC.Effect
module DsEnv = FStarC.Syntax.DsEnv

(* Neither is reached from the compiler's own roots, so this unit compiles
   them itself, and their bodies use the compiler's [string] hash table. *)
let exported (env:DsEnv.env) (l:Ident.lident) : ML (list string) =
  DsEnv.transitive_exported_ids env l

let has_sigelt (env:DsEnv.env) (l:Ident.lident) : ML bool =
  Some? (DsEnv.try_lookup_sigelt env l)

let _ = FStarC.Format.print_string "CustardFunctorLink: loaded\n"

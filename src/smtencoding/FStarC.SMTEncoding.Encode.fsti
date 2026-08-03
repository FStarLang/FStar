(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.SMTEncoding.Encode
open FStarC.Effect
open FStarC.SMTEncoding.Term
module ErrorReporting = FStarC.SMTEncoding.ErrorReporting
module S = FStarC.Syntax.Syntax
module Env = FStarC.TypeChecker.Env
type encoding_depth = int & int
val get_current_env: Env.env -> ML FStarC.SMTEncoding.Env.env_t
(* Registering a dependency module's SMT encoding with the solver, and reading it
   out of that module's .checked file in the first place, is pure waste for a
   client that never talks to the solver.  So [FStarC.Universal] hands those
   encodings to [defer_encoding] instead of performing them, in dependency
   order, and they are run by [flush_deferred_encodings].

   A deferred encoding must be replayed at the solver context depth at which the
   module was loaded, since a subsequent pop would otherwise discard it.  Hence
   every entry point that may push a context, or that needs the encoding
   environment or the solver to be up to date, flushes first. *)
val defer_encoding: (unit -> ML unit) -> ML unit
val flush_deferred_encodings: unit -> ML unit

val init: Env.env -> ML unit
val snapshot_encoding: string -> ML encoding_depth
val rollback_encoding: string -> option encoding_depth -> ML unit
val push_encoding_state: string -> ML unit
val pop_encoding_state:  string -> ML unit
val encode_sig: Env.env -> S.sigelt -> ML unit
val encode_modul: Env.env -> S.modul -> ML FStarC.SMTEncoding.Env.module_encoding
(* Computes the encoding, but does not hand it to the solver nor record it in the
   global encoding environment. Used for the interface of the module that is
   about to be checked. *)
val encode_modul_no_solver: Env.env -> S.modul -> ML FStarC.SMTEncoding.Env.module_encoding
//the lident is the module name
val encode_modul_from_cache: Env.env -> S.modul -> FStarC.SMTEncoding.Env.module_encoding -> ML unit
val encode_query: option (unit -> ML string)
                -> Env.env
                -> S.term
                -> ML (list decl  //prelude, translation of tcenv
                  & ErrorReporting.goal_tree) //the goals of the query

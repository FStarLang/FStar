﻿(*
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
module FStarC.SMTEncoding.Z3
open FStarC.Effect
open FStarC
open FStarC.SMTEncoding.Term
open FStarC.BaseTypes
open FStarC.Util
module U = FStarC.SMTEncoding.UnsatCore
module SolverState = FStarC.SMTEncoding.SolverState

type z3status =
    | UNSAT   of option U.unsat_core
    | SAT     of error_labels & option string         //error labels & z3 reason
    | UNKNOWN of error_labels & option string         //error labels & z3 reason
    | TIMEOUT of error_labels & option string         //error labels & z3 reason
    | KILLED
type z3statistics = SMap.t string

type z3result = {
      z3result_status      : z3status;
      z3result_time        : int;
      z3result_statistics  : z3statistics;
      z3result_query_hash  : option string;
      z3result_log_file    : option string
}

type query_log = {
    get_module_name: unit -> string;
    set_module_name: string -> unit;
    write_to_log:    bool -> string -> string; (* returns name of log file written to *)
    append_to_log:   string -> string; (* idem *)
    close_log:       unit -> unit;
}

val status_string_and_errors : z3status -> string & error_labels

val giveZ3 : list decl -> unit

val ask_text
       : r:Range.range
       -> cache:(option string) // hash
       -> label_messages:error_labels
       -> qry:list decl
       -> queryid:string
       -> core:option U.unsat_core
       -> string

val ask: r:Range.range
       -> cache:option string // hash
       -> label_messages:error_labels
       -> qry:list decl
       -> queryid:string
       -> fresh:bool
       -> core:option U.unsat_core
       -> z3result

(* This will make sure the solver is in a fresh state, potentially
killing the current process. A new process will *not* be started
until we actually need to perform a query. *)
val refresh: option SolverState.using_facts_from_setting -> unit

(* Kill the current background Z3 process. *)
val stop : unit -> unit

val push : msg:string -> unit
val pop : msg:string -> unit
val snapshot : string -> int
val rollback : string -> option int -> unit
val start_query (msg:string) (prefix_to_push:list decl) (query:decl) : unit
val finish_query (msg:string) : unit
val query_logging : query_log

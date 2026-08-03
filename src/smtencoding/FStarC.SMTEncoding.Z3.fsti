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
module FStarC.SMTEncoding.Z3
open FStarC.Effect
open FStarC
open FStarC.SMTEncoding.Term
open FStarC.BaseTypes
module SolverState = FStarC.SMTEncoding.SolverState

type z3status =
    | UNSAT
    | SAT     of option string         //z3 reason
    | UNKNOWN of option string         //z3 reason
    | TIMEOUT of option string         //z3 reason
    | KILLED
type z3statistics = SMap.t string

type z3result = {
      z3result_status      : z3status;
      z3result_time        : int;
      z3result_initial_statistics : z3statistics;
      z3result_statistics  : z3statistics;
      z3result_log_file    : option string
}

type query_log = {
    get_module_name: unit -> ML string;
    set_module_name: string -> ML unit;
    write_to_log:    bool -> string -> ML string; (* returns name of log file written to *)
    append_to_log:   string -> ML string; (* idem *)
    close_log:       unit -> ML unit;
}

val status_string : z3status -> ML string

val query_logging : query_log

val giveZ3 : list decl -> ML unit

(* Give the solver a whole module's SMT encoding, without deserializing it;
   see FStarC.SMTEncoding.SolverState.lazy_decls *)
val giveZ3_lazy : SolverState.lazy_decls -> ML unit

val ask_text
       : r:Range.t
       -> qry:list decl
       -> queryid:string
       -> ML string

(* Asks the solver a batch of queries.  [qry] may contain any number of
   check-sat blocks, each delimited by [Echo "<goal>"] / [Echo "</goal>"];
   one result is returned per block that the solver answered.  Fewer results
   than blocks means the solver died part-way through. *)
val ask: r:Range.t
       -> qry:list decl
       -> queryid:string
       -> fresh:bool
       -> ML (list z3result)

(* This will make sure the solver is in a fresh state, potentially
killing the current process. A new process will *not* be started
until we actually need to perform a query. *)
val refresh: option SolverState.using_facts_from_setting -> ML unit

(* Kill the current background Z3 process. *)
val stop : unit -> ML unit

val push : msg:string -> ML unit
val pop : msg:string -> ML unit
val snapshot : string -> ML int
val rollback : string -> option int -> ML unit
val start_query (msg:string) (prefix_to_push:list decl) (query:decl) : ML unit
val finish_query (msg:string) : ML unit

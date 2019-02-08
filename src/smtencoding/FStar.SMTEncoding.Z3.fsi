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
#light "off"

module FStar.SMTEncoding.Z3
open FStar.ST
open FStar.All
open FStar
open FStar.SMTEncoding.Term
open FStar.BaseTypes
open FStar.Util
module BU = FStar.Util

type unsat_core = option<list<string>>
type scope_t = list<list<decl>>
type z3status =
    | UNSAT   of unsat_core
    | SAT     of error_labels * option<string>         //error labels * z3 reason
    | UNKNOWN of error_labels * option<string>         //error labels * z3 reason
    | TIMEOUT of error_labels * option<string>         //error labels * z3 reason
    | KILLED
val status_string_and_errors : z3status -> string * error_labels
type z3statistics = BU.smap<string>
val set_z3_options : string -> unit

type z3result = {
      z3result_status      : z3status;
      z3result_time        : int;
      z3result_statistics  : z3statistics;
      z3result_query_hash  : option<string>;
      z3result_log_file    : option<string>
}
type cb = z3result -> unit
val giveZ3 : list<decl> -> unit
val ask: r:Range.range
       -> filter:(decls_t -> decls_t * bool)
       -> cache:(option<string>) // hash
       -> label_messages:error_labels
       -> qry:list<decl>
       -> scope:option<scope_t>
       -> cb:cb
       -> fresh:bool
       -> unit

val refresh: unit -> unit
val finish: unit -> unit
val mk_fresh_scope: unit -> scope_t
val init : unit -> unit
val push : msg:string -> unit
val pop : msg:string -> unit
val snapshot : msg:string -> (int * unit)
val rollback : msg:string -> option<int> -> unit

type query_log = {
    get_module_name: unit -> string;
    set_module_name: string -> unit;
    write_to_log:    bool -> string -> string;
    close_log:       unit -> unit
}
val query_logging : query_log

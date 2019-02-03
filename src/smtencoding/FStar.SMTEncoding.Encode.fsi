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

module FStar.SMTEncoding.Encode
open FStar.ST
open FStar.All
open FStar.SMTEncoding.Term
module ErrorReporting = FStar.SMTEncoding.ErrorReporting
module S = FStar.Syntax.Syntax
module Env = FStar.TypeChecker.Env

val push: string -> unit
val pop:  string -> unit
val snapshot: string -> (Env.solver_depth_t * unit)
val rollback: string -> option<Env.solver_depth_t> -> unit
val init: Env.env -> unit
val encode_sig: Env.env -> S.sigelt -> unit
val encode_modul: Env.env -> S.modul -> decls_t * list<Env.fvar_binding>
val encode_query: option<(unit -> string)>
                -> Env.env
                -> S.term
                ->  list<decl>  //prelude, translation of tcenv
                  * list<ErrorReporting.label> //labels in the query
                  * decl        //the query itself
                  * list<decl>  //suffix, evaluating labels in the model, etc

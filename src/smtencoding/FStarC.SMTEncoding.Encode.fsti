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
val init: Env.env -> ML unit
val snapshot_encoding: string -> ML encoding_depth
val rollback_encoding: string -> option encoding_depth -> ML unit
val push_encoding_state: string -> ML unit
val pop_encoding_state:  string -> ML unit
val encode_sig: Env.env -> S.sigelt -> ML unit
val encode_modul: Env.env -> S.modul -> ML (decls_t & list FStarC.SMTEncoding.Env.fvar_binding)
//the lident is the module name
val encode_modul_from_cache: Env.env -> S.modul -> (decls_t & list FStarC.SMTEncoding.Env.fvar_binding) -> ML unit
val encode_query: option (unit -> ML string)
                -> Env.env
                -> S.term
                -> ML (list decl  //prelude, translation of tcenv
                  & list ErrorReporting.label //labels in the query
                  & decl        //the query itself
                  & list decl)  //suffix, evaluating labels in the model, etc
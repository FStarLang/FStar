(*
   Copyright 2008-2018 Microsoft Research

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

module FStarC.CheckedFiles
open FStarC.Effect
open FStarC
open FStarC.Util
open FStarC.TypeChecker.Env
open FStarC.Syntax

module Syntax  = FStarC.Syntax.Syntax
module Dep     = FStarC.Parser.Dep
module TcEnv   = FStarC.TypeChecker.Env

val cache_version_number : int

(*
 * This is what is returned when clients read a module from the caches
 *)
type tc_result = {
  checked_module: Syntax.modul; //persisted
  mii:DsEnv.module_inclusion_info; //persisted
  smt_decls:(FStarC.SMTEncoding.Term.decls_t &  //list of smt decls and fvbs for the module
             list FStarC.SMTEncoding.Env.fvar_binding); //persisted

  tc_time:int;
  extraction_time:int
}

val load_tc_result (checked_fn:string) : option (list (string & string) & tc_result)

val load_checked_file_with_tc_result
  (deps:Dep.deps)
  (fn:string)
  (checked_fn:string)
  : either string tc_result

(*
 * Read parsing data from the checked file
 * This function is passed as a callback to Parser.Dep
 *
 * Input is the file name, not the cache file name
 * The function computes the cache file name itself
 *)
val load_parsing_data_from_cache: file_name:string -> option Parser.Dep.parsing_data

(***********************************************************************)
(* Loading and storing cache files                                     *)
(***********************************************************************)

val load_module_from_cache: TcEnv.env -> string -> option tc_result

val store_module_to_cache: TcEnv.env -> file_name:string -> Dep.parsing_data -> tc_result -> unit

val unsafe_raw_load_checked_file (checked_file_name:string)
  : option (FStarC.Parser.Dep.parsing_data & list string & tc_result)

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

  //The SMT encoding of the module. Its index and fvar bindings are persisted
  //alongside the module, but the declarations themselves are persisted as a
  //separate value in the checked file and are only read (once) if the thunk is
  //ever forced: they account for the majority of a checked file's size, and are
  //typically not needed at all, since context pruning discards most of a
  //dependency's declarations for any given query.
  smt_encoding: FStarC.SMTEncoding.Env.module_encoding;

  tc_time:int;
  extraction_time:int
}

val load_tc_result (checked_fn:string) : ML (option (list (string & string) & tc_result))

val load_checked_file_with_tc_result
  (deps:Dep.deps)
  (fn:string)
  (checked_fn:string)
  : ML (either string tc_result)

(*
 * Read parsing data from the checked file
 * This function is passed as a callback to Parser.Dep
 *
 * Input is the file name, not the cache file name
 * The function computes the cache file name itself
 *)
val load_parsing_data_from_cache: file_name:string -> ML (option Parser.Dep.parsing_data)

(***********************************************************************)
(* Loading and storing cache files                                     *)
(***********************************************************************)

//checks if the cache files exists and all their dependences are valid
//returning the names of all the dependences if so
val scan_deps_and_check_cache_validity (file:string) : ML (option (list string & Dep.deps))

val load_module_from_cache: TcEnv.env -> string -> ML (option tc_result)

val store_module_to_cache:
    TcEnv.env ->
    file_name: string ->
    parsing_data_and_direct_deps: (Dep.parsing_data & list string) ->
    tc_result ->
    ML unit

val unsafe_raw_load_checked_file (checked_file_name:string)
  : ML (option (FStarC.Parser.Dep.parsing_data & list string & tc_result))
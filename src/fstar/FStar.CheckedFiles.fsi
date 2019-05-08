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
#light "off"

module FStar.CheckedFiles
open FStar.ST
open FStar.Exn
open FStar.All
open FStar
open FStar.Util
open FStar.Extraction.ML.UEnv
open FStar.Syntax.DsEnv

module Syntax  = FStar.Syntax.Syntax
module Dep     = FStar.Parser.Dep

(*
 * This is what is returned when clients read a module from the caches
 *)
type tc_result = {
  checked_module: Syntax.modul; //persisted
  mii:module_inclusion_info; //persisted
  smt_decls:(FStar.SMTEncoding.Term.decls_t *  //list of smt decls and fvbs for the module
             list<FStar.SMTEncoding.Env.fvar_binding>); //persisted

  tc_time:int;
  extraction_time:int
}

(*
 * Read parsing data from the checked file
 * This function is passed as a callback to Parser.Dep
 *
 * Input is the file name, not the cache file name
 * The function computes the cache file name itself
 *)
val load_parsing_data_from_cache: file_name:string -> option<Parser.Dep.parsing_data>

(***********************************************************************)
(* Loading and storing cache files                                     *)
(***********************************************************************)

val load_module_from_cache: (uenv -> string -> option<tc_result>)

val store_module_to_cache: uenv -> file_name:string -> Dep.parsing_data -> tc_result -> unit 

(*
   Copyright 2008-2016 Jonathan Protzenko, Nikhil Swamy and Microsoft Research

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

// A dependency-finding routine
module FStarC.Dependencies
open FStarC
open FStarC.Effect

(***********************************************************************)
(* Finding the transitive dependencies of a list of files               *)
(***********************************************************************)

(*
 * get_parsing_data_from_cache is a callback passed to Parser.Dep for
 *   getting deps from the checked files
 *)
let find_deps_if_needed files
  (get_parsing_data_from_cache:string -> option Parser.Dep.parsing_data)
  = let all_files, deps = Parser.Dep.collect files get_parsing_data_from_cache in
    match all_files with
    | [] ->
        Errors.log_issue0 Errors.Error_DependencyAnalysisFailed "Dependency analysis failed; reverting to using only the files provided";
        files,
        deps
    | _ ->
        List.rev all_files,
        deps

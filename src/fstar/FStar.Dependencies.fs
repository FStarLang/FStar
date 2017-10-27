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
#light "off"

// A dependency-finding routine
module FStar.Dependencies
open FStar.ST
open FStar.All
open FStar
open FStar.Util
open FStar.Getopt
open FStar.Ident

(***********************************************************************)
(* Finding the transitive dependencies of a list of files               *)
(***********************************************************************)
let find_deps_if_needed files =
    let all_files, _ = Parser.Dep.collect files in
    match all_files with
    | [] ->
        Util.print_error "Dependency analysis failed; reverting to using only the files provided\n";
        files
    | _ ->
        let all_files = List.rev all_files in
        let all_files_except_prims =
          let prims = Options.prims_basename () in
          if basename (List.hd all_files) = prims then
            List.tl all_files
          else begin
            Util.print1_error "Dependency analysis did not find prims module %s?!\n" prims;
            exit 1
          end
        in
        all_files_except_prims

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
let find_deps_if_needed verify_mode files =
  if Options.explicit_deps () then
    files
  else
    let _, deps, _ = Parser.Dep.collect verify_mode files in
    match deps with
    | [] ->
        Util.print_error "Dependency analysis failed; reverting to using only the files provided\n";
        files
    | _ ->
        let deps = List.rev deps in
        let deps =
          let prims = Options.prims_basename () in
          if basename (List.hd deps) = prims then
            List.tl deps
          else begin
            Util.print1_error "Dependency analysis did not find prims module %s?!\n" prims;
            exit 1
          end
        in
        deps

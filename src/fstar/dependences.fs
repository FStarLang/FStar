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

//Batch-mode type-checking for the stratified type-checker
module FStar.Dependences
open FStar
open FStar.Util
open FStar.Getopt
open FStar.Ident

(***********************************************************************)
(* Finding the transitive dependences of a list of files               *)
(***********************************************************************)
let find_deps_if_needed files =
  if !Options.explicit_deps then
    files, []
  else
    let _, deps = Parser.Dep.collect files in
    let deps = List.rev deps in
    let deps =
      if basename (List.hd deps) = "prims.fst" then
        List.tl deps
      else begin
        Util.print_error "dependency analysis did not find prims.fst?!";
        exit 1
      end
    in
    let admit_fsi = ref [] in
    List.iter (fun d ->
              let d = basename d in
              if get_file_extension d = "fsti" then
                admit_fsi := substring d 0 (String.length d - 5) :: !admit_fsi
              else if get_file_extension d = "fsi" then begin
                admit_fsi := substring d 0 (String.length d - 4) :: !admit_fsi end
    ) deps;
    deps, !admit_fsi


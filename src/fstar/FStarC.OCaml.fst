(*
   Copyright 2008-2016 Nikhil Swamy and Microsoft Research

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
module FStarC.OCaml

open FStarC
open FStar.List.Tot.Base
open FStarC
open FStarC.Effect

let shellescape (s:string) : string =
  String.list_of_string s |>
  List.map (function
    | '\'' -> "'\"'\"'" // to escape single quotes we need to put them inside a double quote
    | c -> String.make 1 c
  ) |>
  String.concat ""

let new_ocamlpath () : string =
  let ocamldir = Find.locate_ocaml () in
  let old_ocamlpath = Option.dflt "" (Util.expand_environment_variable "OCAMLPATH") in
  let new_ocamlpath = ocamldir ^ Platform.ocamlpath_sep ^ old_ocamlpath in
  new_ocamlpath

let exec_in_ocamlenv #a (cmd : string) (args : list string) : a =
  let new_ocamlpath = new_ocamlpath () in
  (* Update OCAMLPATH and run the command *)
  Util.putenv "OCAMLPATH" new_ocamlpath;
  let pid = Util.create_process cmd (cmd :: args) in
  let rc = Util.waitpid pid in
  match rc with
  | Inl rc -> exit rc
  | Inr _ -> exit 1

let app_lib = "fstar.lib"
let plugin_lib = "fstar.pluginlib"

(* OCaml Warning 8: this pattern-matching is not exhaustive.
This is usually benign as we check for exhaustivenss via SMT. *)
let wstr = "-8"

let common_args =
  "-w" :: wstr ::
  "-thread" ::
  []

let exec_ocamlc args =
  exec_in_ocamlenv "ocamlfind"
    ("c" :: common_args @ "-linkpkg" :: "-package" :: app_lib :: args)

let exec_ocamlopt args =
  exec_in_ocamlenv "ocamlfind"
    ("opt" :: common_args @ "-linkpkg" :: "-package" :: app_lib :: args)

let exec_ocamlopt_plugin args =
  exec_in_ocamlenv "ocamlfind"
    ("opt" :: common_args @ "-shared" :: "-package" :: plugin_lib :: args)

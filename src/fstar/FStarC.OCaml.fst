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
open FStarC.Effect

let shellescape (s:string) : string =
  String.list_of_string s |>
  FStar.List.Tot.Base.map (function
    | '\'' -> "'\"'\"'" // to escape single quotes we need to put them inside a double quote
    | c -> FStar.String.make 1 c
  ) |>
  String.concat ""

let new_ocamlpath () : ML string =
  let ocamldir = Find.locate_ocaml () in
  let old_ocamlpath = Option.dflt "" (Util.expand_environment_variable "OCAMLPATH") in
  let new_ocamlpath = ocamldir ^ Platform.ocamlpath_sep ^ old_ocamlpath in
  new_ocamlpath

let exec_in_ocamlenv #a (cmd : string) (args : list string) : ML a =
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

(* True iff findlib can resolve [pkg] in the current (ambient) OCaml
   environment. We use the findlib library (via Util.findlib_package_exists)
   rather than spawning `ocamlfind`, so this works on native Windows (no shell
   required). We deliberately query the ambient environment, NOT fstar.exe's
   bundled OCAMLPATH, so the result reflects the user's current opam switch
   rather than the library shipped with this fstar.exe. *)
let ocamlfind_query (pkg:string) : ML bool =
  Util.findlib_package_exists pkg

let install_lib () : ML int =
  if ocamlfind_query app_lib then begin
    Format.print1_error "%s is already installed; nothing to do.\n" app_lib;
    0
  end
  else if ocamlfind_query "fstar" then begin
    Format.print_error
      "An 'fstar' findlib package is already installed in the current \
environment, but it does not provide fstar.lib. Refusing to install fstar.lib, \
since doing so would overwrite the package's META file and drop its other \
sub-packages (e.g. fstar.compiler, fstar.pluginlib). Install fstar.lib into a \
separate switch, or (re)install F* via opam.\n";
    1
  end
  else
    match Find.lib_root () with
    | None ->
      Format.print_error
        "Could not locate the F* library (is --no_default_includes set?).\n";
      1
    | Some root ->
      let dir = root ^ "/lib" in
      let installer = dir ^ "/install.sh" in
      if not (Filepath.file_exists installer) then begin
        Format.print1_error
          "This F* installation does not ship the fstar.lib sources (expected an \
installer at %s). Only binary or source packages carry them.\n" installer;
        1
      end
      else
        Util.system_run (Format.fmt1 "bash '%s'" (shellescape installer))

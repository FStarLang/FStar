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

(* True iff findlib can resolve [pkg] in the OCaml environment currently in
   effect (i.e. the current OCAMLPATH/OCAMLFIND_CONF). We use the findlib
   library (via Util.findlib_package_exists) rather than spawning `ocamlfind`,
   so this works on native Windows (no shell required). [Findlib.init] re-reads
   OCAMLPATH on each call, so the result follows any OCAMLPATH we set before
   calling: install_lib_aux extends OCAMLPATH with fstar.exe's bundled library
   dir (as --ocamlenv does) so this query sees both the user's opam switch and
   a compiled fstar.lib shipped alongside this fstar.exe. *)
let ocamlfind_query (pkg:string) : ML bool =
  Util.findlib_package_exists pkg

(* Spawn [prog] with [args] (no shell), inheriting our stdio, and return its
   exit code (or 1 if it was killed by a signal). Unlike a shell invocation,
   this works on native Windows. *)
let run_prog (prog:string) (args:list string) : ML int =
  let pid = Util.create_process prog (prog :: args) in
  match Util.waitpid pid with
  | Inl rc -> rc
  | Inr _ -> 1

(* Install fstar.lib's OCaml dependencies into the current opam switch, using
   the fstar-lib.opam file shipped at [root] (= <lib_root>, the parent of the
   dune project directory; we keep it out of the dune project dir so that
   `dune build` does not pick it up as a package). We drive opam directly
   (no shell) via `opam install --deps-only -y <file>`. The opam file is
   intentionally not buildable (build: false), so `--deps-only` installs only
   its dependencies and never tries to build a package. Errors out if the opam
   file is missing. *)
let install_lib_deps (root:string) : ML int =
  let opam_file = root ^ "/fstar-lib.opam" in
  if not (Filepath.file_exists opam_file) then begin
    Format.print1_error
      "This F* installation does not ship fstar.lib's opam dependency file \
(expected %s). Only binary or source packages carry it; use --install_lib if \
the dependencies are already installed.\n" opam_file;
    1
  end
  else
    run_prog "opam" ["install"; "--deps-only"; "-y"; opam_file]

let install_lib_aux (with_deps:bool) : ML int =
  (* Extend OCAMLPATH with fstar.exe's bundled library dir (<exec>/../lib),
     exactly as --ocamlenv does, before the detection below. This way the
     "is fstar.lib already available?" check also sees a compiled fstar.lib
     shipped alongside this fstar.exe -- as in a source build, `make install`
     or `opam install` -- and reports it as already installed (a no-op),
     making `--install_lib[_with_deps]` behave uniformly across all install
     methods. For a binary package the bundled dir ships no findlib metadata,
     so this is a no-op extension and we proceed to build+install fstar.lib
     into the current opam switch as before. (This command then exits, so
     mutating the process environment here is harmless.) *)
  Util.putenv "OCAMLPATH" (new_ocamlpath ());
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
      (* Binary/source packages ship the fstar.lib OCaml sources together with a
         dune project under <lib_root>/lib. We build and install them by driving
         dune directly (no shell), so this works on native Windows too. We do not
         pass --prefix, so dune installs into the current opam switch; and we do
         not need to merge META, since we already refused above if an 'fstar'
         findlib package was present (so dune writes a fresh fstar/META here). *)
      let dir = root ^ "/lib" in
      let dune_project = dir ^ "/dune-project" in
      if not (Filepath.file_exists dune_project) then begin
        Format.print1_error
          "This F* installation does not ship the fstar.lib sources (expected a \
dune project at %s). Only binary or source packages carry them.\n" dune_project;
        1
      end
      else
        (* When requested, first install fstar.lib's dependencies via opam, so
           that the subsequent dune build can succeed. The opam file lives at
           [root] (parent of the dune project dir). *)
        let deps_rc = if with_deps then install_lib_deps root else 0 in
        if deps_rc <> 0 then deps_rc
        else
          let rc = run_prog "dune" ["build"; "--root"; dir] in
          if rc <> 0 then rc
          else run_prog "dune" ["install"; "--root"; dir]

let install_lib () : ML int = install_lib_aux false

let install_lib_with_deps () : ML int = install_lib_aux true

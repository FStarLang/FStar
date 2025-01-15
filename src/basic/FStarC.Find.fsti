(*
   Copyright 2008-2024 Microsoft Research

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
module FStarC.Find
(* Utilities for finding files in the include path and related
operations. *)

open FStarC.Effect

(* A bit silly to have this, but this is the directory where the fstar.exe executable is in. *)
val fstar_bin_directory : string

(* The root directory of the F* library, if any *)
val lib_root () : option string

(* The full include path. We search files in all of these directories. *)
val include_path () : list string

(* Try to find a file in the include path with a given basename. *)
val find_file (basename : string) : option string

(* As above, but also looks in the output directory (--odir). This is useful to find
plugins that we might have created. *)
val find_file_odir (basename : string) : option string

val prepend_cache_dir           : string  -> string
val prepend_output_dir          : string  -> string

(* Return absolute path of directory where fstar.exe lives *)
val locate () : string

(* Return absolute path of F* library, if any.
(this will be empty with --no_default_includes) *)
val locate_lib () : option string

(* Return absolute path of OCaml-installed components of F*. *)
val locate_ocaml () : string

(* A message for the user suggesting how to install the proper Z3 version. *)
val z3_install_suggestion (v : string) : list Pprint.document

(* Locate executable for Z3 version [v]. *)
val locate_z3 (v : string) : option string

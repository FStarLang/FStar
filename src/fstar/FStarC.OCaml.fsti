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

open FStarC.Effect

(* Escape a string for use in a shell command, expecting to be wrapped in SINGLE quotes. *)
val shellescape (s:string) : string

(* Compute a value for OCAMLPATH taken from the current env + extended with our own library.
This is NOT escaped. *)
val new_ocamlpath () : string

(* Run a command with the new OCAMLPATH set. This calls execvp, so it
will not return if successful. Raises a Failure if the execvp fails. It
also tries to find the command in the PATH, absolute path is not needed.
*)
val exec_in_ocamlenv (#a:Type) (cmd : string) (args : list string) : a

(* Run ocamlc (i.e. bytecode compiler) passing appropriate flags to
generate a bytecode executable. Expects the source file and further
options as arguments. *)
val exec_ocamlc #a (args : list string) : a

(* Run ocamlopt (i.e. native compiler) passing appropriate flags to
generate an executable. Expects the source file and further options as
arguments. *)
val exec_ocamlopt #a (args : list string) : a

(* Run ocamlc passing appropriate flags to generate an F* plugin,
using fstar.pluginlib. Expects the source file and further options as
arguments. *)
val exec_ocamlopt_plugin #a (args : list string) : a

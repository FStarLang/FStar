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
module FStarC.Find.Z3

(* Utilities for finding z3 *)

open FStarC
open FStarC.Effect

(* A message for the user suggesting how to install the proper Z3 version. *)
val z3_install_suggestion (v : string) : list Pprint.document

(* Locate executable for Z3 version [v]. *)
val locate_z3 (v : string) : option string

(*
   Copyright 2008-2017  Microsoft Research

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
(* -------------------------------------------------------------------- *)
module FStarC.Extraction.Krml

open FStarC
open FStarC.Class.Show

type version = int
val current_version: version (* version of AST type, for binary compatibility *)

val decl : Type0

instance val showable_decl : showable decl

type program = list decl
type file = string & program

(** Versioned binary writing/reading of ASTs.
    Serialization/parsing is with output_value/input_value. *)
type binary_format = version & list file

val translate : Extraction.ML.UEnv.uenv -> list Extraction.ML.Syntax.mlmodule -> list file

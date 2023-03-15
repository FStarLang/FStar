﻿(*
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
module FStar.Extraction.Krml

val decl : Type0
type program = list decl
type file = string * program

(** Versioned binary writing/reading of ASTs *)
type version = int
type binary_format = version * list file

val current_version: version
val translate : FStar.Extraction.ML.Syntax.mllib -> list file

(* Called by FStar.Main.main () to initialize code translators *)
val init : unit -> FStar.Compiler.Effect.ML unit

﻿(*
  Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStar.ToSyntax.Interleave
open FStar.Compiler.Effect
open FStar.Compiler.Effect
open FStar.Ident
open FStar.Parser.AST

(* GM: If I don't use the full name, I cannot bootstrap *)

val initialize_interface:        lident -> list decl -> FStar.Syntax.DsEnv.withenv unit
val prefix_with_interface_decls: lident -> decl -> FStar.Syntax.DsEnv.withenv (list decl)
val interleave_module:           modul -> bool -> FStar.Syntax.DsEnv.withenv modul

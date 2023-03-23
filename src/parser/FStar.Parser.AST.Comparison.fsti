(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: N. Swamy and Copilot
*)
module FStar.Parser.AST.Comparison
open FStar.Pervasives
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar.Parser.AST

(* Check if two decls are equal, ignoring range metadata.
   Used in FStar.Interactive.Incremental *)
val eq_decl (d1 d2:decl) : bool

val lidents_of_term (t:term) : list FStar.Ident.lident
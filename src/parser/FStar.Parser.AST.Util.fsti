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
module FStar.Parser.AST.Util
open FStar.Pervasives
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar.Parser.AST

(* Check if two decls are equal, ignoring range metadata.
   Used in FStar.Interactive.Incremental *)
val eq_decl (d1 d2:decl) : bool

val lidents_of_decl (t:decl) : list FStar.Ident.lident

type open_namespaces_and_abbreviations = {
   open_namespaces: list FStar.Ident.lident;
   module_abbreviations: list (FStar.Ident.ident * FStar.Ident.lident);
}

type error_message = {
   message: string;
   range: FStar.Compiler.Range.range;
}

type extension_parser = 
   open_namespaces_and_abbreviations ->
   contents:string ->
   p:FStar.Compiler.Range.range ->
   either error_message decl'

val register_extension_parser (extension_name:string) (parser:extension_parser) : unit
val lookup_extension_parser (extension_name:string) : option extension_parser
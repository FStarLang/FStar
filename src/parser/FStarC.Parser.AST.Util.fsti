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
module FStarC.Parser.AST.Util
open FStarC.Effect
open FStarC.List
open FStarC.Parser.AST

(* Check if two decls are equal, ignoring range metadata.
   Used in FStarC.Interactive.Incremental *)
val eq_term (t1 t2:term) : bool
val eq_binder (b1 b2:binder) : bool
val eq_pattern (p1 p2:pattern) : bool
val eq_decl (d1 d2:decl) : bool

val lidents_of_decl (t:decl) : list FStarC.Ident.lident

type open_namespaces_and_abbreviations = {
   open_namespaces: list FStarC.Ident.lident;
   module_abbreviations: list (FStarC.Ident.ident & FStarC.Ident.lident);
}

type error_message = {
   message: list FStarC.Pprint.document;
   range: FStarC.Range.range;
}

type extension_parser = {
  parse_decl_name:
    (contents:string ->
     FStarC.Range.range ->
     either error_message FStarC.Ident.ident);

  parse_decl:
   (open_namespaces_and_abbreviations ->
    contents:string ->
    p:FStarC.Range.range ->
    either error_message decl)
}

val register_extension_parser (extension_name:string) (parser:extension_parser) : unit
val lookup_extension_parser (extension_name:string) : option extension_parser


type extension_lang_parser = {
  parse_decls:
   (contents:string ->
    p:FStarC.Range.range ->
    either error_message (list decl))
}

val as_open_namespaces_and_abbrevs (ls:list decl) : open_namespaces_and_abbreviations
val register_extension_lang_parser (extension_name:string) (parser:extension_lang_parser) : unit
val lookup_extension_lang_parser (extension_name:string) : option extension_lang_parser
val parse_extension_lang (lang_name:string) (raw_text:string) (raw_text_pos:FStarC.Range.range) : list decl

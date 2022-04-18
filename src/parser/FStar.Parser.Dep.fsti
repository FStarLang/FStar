(*
   Copyright 2008-2014 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR C  ONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.Parser.Dep
open FStar.Compiler.Effect
open FStar
open FStar.Compiler
open FStar.Parser
open FStar.Parser.AST
open FStar.Compiler.Util
open FStar.Const
open FStar.String
open FStar.Ident
open FStar.Errors
module Const = FStar.Parser.Const
module BU = FStar.Compiler.Util

type open_kind = | Open_module | Open_namespace

val module_name_of_file : string -> string
val lowercase_module_name : string -> string

val build_inclusion_candidates_list : unit -> list (string * string)

val core_modules  : list string
(* Given a filename, returns the list of automatically opened modules
and namespaces *)
val hard_coded_dependencies : string -> list (lident * open_kind)

val is_interface: string -> bool
val is_implementation: string -> bool
type module_name = string
type parsing_data  //cached in the checked files
val empty_parsing_data: parsing_data  //for legacy ide
type deps
val empty_deps : deps
val interface_of : deps -> module_name:string -> option string  //return value is the file name
val implementation_of : deps -> module_name:string -> option string  //return value is the file name
val cache_file_name: (string -> string)
val parsing_data_of: deps -> string -> parsing_data
val collect: list string -> (string -> option parsing_data) -> list string * deps
val deps_of : deps -> string -> list string
val print : deps -> unit
val print_digest: list (string * string) -> string
val module_has_interface: deps -> module_name:Ident.lident -> bool
val deps_has_implementation: deps -> module_name:Ident.lident -> bool
val print_raw: deps -> unit

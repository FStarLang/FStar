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
module FStarC.Parser.Dep

open FStarC
open FStarC.Effect
open FStarC.Ident
open FStarC.Util { out_channel }

val fly_deps_enabled () : bool
val with_fly_deps_disabled (f:unit -> 'a) : 'a
val debug_fly_deps () : bool
(*
 * AR: Parsing data for a file (also cached in the checked files)
 *     It is a summary of opens, includes, A.<id>, etc. in a module
 *     Earlier we used to store the dependences in the checked file,
 *       however that is an image of the file system, and so, when the checked
 *       files were used in a slightly different file system, there were strange errors
 *       see e.g. #1657 for a couple of cases
 *     Now we store the following summary and construct the dependences from the current
 *       file system
 *)

type open_kind = | Open_module | Open_namespace

type parsing_data_elt =
  | P_begin_module of lident  //begin_module
  | P_open of (*let open*)bool & lident  //record_open
  | P_implicit_open_module_or_namespace of (open_kind & lid)  //record_open_module_or_namespace
  | P_dep of bool & lident  //add_dep_on_module, bool=true iff it's a friend dependency
  | P_alias of ident & lident  //record_module_alias
  | P_lid of lident  //record_lid
  | P_inline_for_extraction

type module_name = string

val maybe_module_name_of_file : string -> option string
val module_name_of_file : string -> string
val lowercase_module_name : string -> string
val build_inclusion_candidates_list : unit -> list (string & string)

val prelude : list (open_kind & lid)

val is_interface: string -> bool
val is_implementation: string -> bool
val parsing_data : Type0  //cached in the checked files
val str_of_parsing_data (p:parsing_data) : string
val empty_parsing_data: parsing_data  //for legacy ide
val friends (p:parsing_data) : list lident
val deps : Type0
val copy_deps (d:deps) : deps 
val empty_deps (cmd_line_files:list string): deps
val is_valid_namespace (d:deps) (ns:lident) : bool
val interface_of : deps -> module_name:string -> option string  //return value is the file name
val implementation_of : deps -> module_name:string -> option string  //return value is the file name
val cache_file_name: (string -> string)
// Scan decls for dependences, key feature for fly_deps
// Typically, ds is just a single decl
// scope_parsing_data is a representing of the current desugaring environment's
// gloabal scope, i.e., the modules and namespaces current open, module abbrevs etc., 
// as parsing data, so that ds can be scanned in the appropriate scope.
val collect_deps_of_decl 
    (deps:deps) (filename:string) (ds:list FStarC.Parser.AST.decl)
    (scope_parsing_data:list parsing_data_elt)
    (get_parsing_data_from_cache:string -> option parsing_data)
: list string //filenames
val collect: list string -> (string -> option parsing_data) -> list string & deps
val deps_of : deps -> string -> list string
val deps_of_modul : deps -> module_name -> list module_name  // list of modules that this module depends on
val parsing_data_of: deps -> string -> parsing_data
val parsing_data_of_modul: deps -> filename:string -> option AST.modul -> parsing_data & list string
val populate_parsing_data: filename:string -> FStarC.Parser.AST.modul -> dep_graph:deps -> unit
val print : deps -> unit
val print_digest: list (string & string) -> string
val module_has_interface: deps -> module_name:Ident.lident -> bool
val deps_has_implementation: deps -> module_name:Ident.lident -> bool
val print_raw: out_channel -> deps -> unit
val all_files: deps -> list string
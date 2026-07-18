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

val debug_fly_deps () : ML bool
val fly_deps_enabled () : ML bool
val with_fly_deps_disabled (f:unit -> ML 'a) : ML 'a

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

val is_interface: string -> ML bool
val is_implementation: string -> ML bool

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
val parsing_data : Type0  //cached in the checked files

val maybe_module_name_of_file : string -> ML (option string)
val module_name_of_file : string -> ML string
val lowercase_module_name : string -> ML string
val str_of_parsing_data (p:parsing_data) : ML string
val friends (p:parsing_data) : ML (list lident)
val empty_parsing_data: parsing_data  //for legacy ide

val deps : Type0
val copy_deps (d:deps) : ML deps
val empty_deps (cmd_line_files:list string): ML deps
val cache_file_name: (string -> ML string)
val build_inclusion_candidates_list : unit -> ML (list (string & string))
val is_valid_namespace (d:deps) (ns:lident) : ML bool
val interface_of : deps -> module_name:string -> ML (option string)  //return value is the file name
val implementation_of : deps -> module_name:string -> ML (option string)  //return value is the file name
val prelude : list (open_kind & lid)

// Scan decls for dependences, key feature for fly_deps
// Typically, ds is just a single decl
// scope_parsing_data is a representing of the current desugaring environment's
// gloabal scope, i.e., the modules and namespaces current open, module abbrevs etc., 
// as parsing data, so that ds can be scanned in the appropriate scope.
val collect_deps_of_decl 
    (deps:deps) (filename:string) (ds:list FStarC.Parser.AST.decl)
    (scope_parsing_data:list parsing_data_elt)
    (get_parsing_data_from_cache:string -> ML (option parsing_data))
: ML (list string) //filenames
val collect: list string -> (string -> ML (option parsing_data)) -> ML (list string & deps)
val parsing_data_of_modul: deps -> filename:string -> option AST.modul -> ML (parsing_data & list string)
val deps_of : deps -> string -> ML (list string)
val deps_of_modul : deps -> module_name -> ML (list module_name)  // list of modules that this module depends on
val parsing_data_of: deps -> string -> ML parsing_data
val populate_parsing_data: filename:string -> FStarC.Parser.AST.modul -> dep_graph:deps -> ML unit
val print_digest: list (string & string) -> ML string
val print_raw: out_channel -> deps -> ML unit
val print : deps -> ML unit
val module_has_interface: deps -> module_name:Ident.lident -> ML bool
val deps_has_implementation: deps -> module_name:Ident.lident -> ML bool
val all_files: deps -> ML (list string)
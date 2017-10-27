#light "off"
module FStar.Parser.Dep
open FStar.ST
open FStar.All
open FStar
open FStar.Parser
open FStar.Parser.AST
open FStar.Parser.Parse
open FStar.Util
open FStar.Const
open FStar.String
open FStar.Ident
open FStar.Errors
module Const = FStar.Parser.Const
module BU = FStar.Util

type file_name = string

type open_kind = | Open_module | Open_namespace

val lowercase_module_name : file_name -> string

val build_inclusion_candidates_list : unit -> list<(string * string)>

(* Given a filename, returns the list of automatically opened modules
and namespaces *)
val hard_coded_dependencies : string -> list<(lident * open_kind)>

val collect_and_memoize: list<file_name> -> list<file_name>

val memoized_deps_of : file_name -> list<file_name>

val print_memoized_deps : unit -> unit

val is_interface: file_name -> bool

val is_implementation: file_name -> bool

val cache_file_name: file_name -> file_name
val hash_dependences: file_name -> option<(list<string>)>
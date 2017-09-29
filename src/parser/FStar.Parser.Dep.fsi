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

(* In case the user passed [--verify_all], we record every single module name we
 * found in the list of modules to be verified.
 * In the [VerifyUserList] case, for every [--verify_module X], we check we
 * indeed find a module [X].
 * In the [VerifyFigureItOut] case, for every file that was on the command-line,
 * we record its module name as one module to be verified.
 *)
type verify_mode =
  | VerifyAll
  | VerifyUserList
  | VerifyFigureItOut

type map = smap<(option<string> * option<string>)>

type color = | White | Gray | Black

type open_kind = | Open_module | Open_namespace

val lowercase_module_name : string -> string

val build_inclusion_candidates_list : unit -> list<(string * string)>
val build_map : list<string> -> map

(* Given a filename, returns the list of automatically opened modules
and namespaces *)
val hard_coded_dependencies : string -> list<(lident * open_kind)>

val collect : verify_mode -> list<string> -> list<(string * list<string>)> * list<string> * BU.smap<(list<string> * color)>

val print : list<(string * list<string>)> * 'a * smap<(list<string> * 'b)> -> unit

val is_interface: string -> bool
val is_implementation: string -> bool

module FStar.Parser.Dep
open FStar
open FStar.Parser
open FStar.Parser.AST
open FStar.Parser.Parse
open FStar.Util
open FStar.Const
open FStar.String
open FStar.Ident
open FStar.Errors
module Const = FStar.Syntax.Const
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

val lowercase_module_name : f:string -> Prims.Tot<string>

val build_map : filenames:list<string> -> map

val collect : verify_mode:verify_mode 
           -> filenames:list<string> 
           -> list<(string * list<string>)>
            * list<string>
            * BU.smap<(list<string> * color)>

val print : make_deps:list<(string * list<string>)> * 'a * graph:smap<(list<string> * 'b)> -> unit
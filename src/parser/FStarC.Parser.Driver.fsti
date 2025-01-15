(*
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
module FStarC.Parser.Driver

module Range      = FStarC.Range
module AST        = FStarC.Parser.AST
module AU         = FStarC.Parser.AST.Util
module ParseIt    = FStarC.Parser.ParseIt

val is_cache_file : string -> bool

type fragment =
    | Empty
    | Modul of AST.modul // an entire module or interface -- unspecified
    | Decls of list AST.decl // a partial set of declarations
    | DeclsWithContent of list (AST.decl & ParseIt.code_fragment)

val parse_fragment : ParseIt.lang_opts -> ParseIt.input_frag -> fragment

(* Returns a non-desugared AST (as in [parser/ast.fs]) or aborts. *)
val parse_file : string -> AST.file & list (string & Range.range)

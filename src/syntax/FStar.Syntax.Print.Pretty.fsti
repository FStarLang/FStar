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

module FStar.Syntax.Print.Pretty

open FStar.Compiler
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Compiler.Util

(* Use these if possible: they abbreviate lidents *)
val term_to_string'     : DsEnv.env -> term -> string
val comp_to_string'     : DsEnv.env -> comp -> string
val sigelt_to_string'   : DsEnv.env -> sigelt -> string

(* If no DsEnv.env is at hand, these can be used instead. *)
val term_to_string      : term -> string
val comp_to_string      : comp -> string
val sigelt_to_string    : sigelt -> string

val univ_to_string      : universe -> string
val tscheme_to_string   : tscheme -> string
val pat_to_string       : pat -> string
val binder_to_string'   : bool -> binder -> string
val eff_decl_to_string' : bool -> Range.range -> list qualifier -> eff_decl -> string

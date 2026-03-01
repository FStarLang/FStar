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

module FStarC.Syntax.Print.Pretty

open FStarC
open FStarC.Effect
open FStarC.Syntax
open FStarC.Syntax.Syntax

(* Use the 'primed' versions if possible: they abbreviate lidents *)

val term_to_doc'     : DsEnv.env -> term -> ML Pprint.document
val univ_to_doc'     : DsEnv.env -> universe -> ML Pprint.document

val term_to_string'     : DsEnv.env -> term -> ML string
val univ_to_string'     : DsEnv.env -> universe -> ML string

val comp_to_doc'     : DsEnv.env -> comp -> ML Pprint.document
val comp_to_string'     : DsEnv.env -> comp -> ML string

val sigelt_to_doc'   : DsEnv.env -> sigelt -> ML Pprint.document
val sigelt_to_string'   : DsEnv.env -> sigelt -> ML string

val term_to_doc         : term -> ML Pprint.document
val univ_to_doc         : universe -> ML Pprint.document
val comp_to_doc         : comp -> ML Pprint.document
val sigelt_to_doc       : sigelt -> ML Pprint.document

val term_to_string      : term -> ML string
val comp_to_string      : comp -> ML string
val sigelt_to_string    : sigelt -> ML string
val univ_to_string      : universe -> ML string

val tscheme_to_doc      : tscheme -> ML Pprint.document
val tscheme_to_string   : tscheme -> ML string

val pat_to_string       : pat -> ML string
val binder_to_string'   : bool -> binder -> ML string
val eff_decl_to_string  : eff_decl -> ML string

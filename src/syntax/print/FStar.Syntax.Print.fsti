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
module FStar.Syntax.Print

open FStar.Compiler.Effect
open FStar.Compiler.Util
open FStar.Const
open FStar.Ident
open FStar.Syntax.Syntax
open FStar.Class.Show
open FStar.Class.PP

module DsEnv = FStar.Syntax.DsEnv
module Json = FStar.Json

val term_to_string'       : DsEnv.env -> term -> string
val comp_to_string'       : DsEnv.env -> comp -> string

val sigelt_to_string'     : DsEnv.env -> sigelt -> string
val sigelt_to_string_short: sigelt -> string

val binder_to_json        : DsEnv.env -> binder -> Json.json
val binders_to_json       : DsEnv.env -> binders -> Json.json

val ctx_uvar_to_string_no_reason    : ctx_uvar -> string

val term_to_doc'          : DsEnv.env -> term -> Pprint.document
val comp_to_doc'          : DsEnv.env -> comp -> Pprint.document
val sigelt_to_doc'        : DsEnv.env -> sigelt -> Pprint.document

val term_to_doc           : term -> Pprint.document
val comp_to_doc           : comp -> Pprint.document
val sigelt_to_doc         : sigelt -> Pprint.document

(* Prints as <u1,..,un>ty instead of a pair *)
val tscheme_to_string : tscheme -> string

(* document *)
val eff_decl_to_string    : bool -> eff_decl -> string

(* Prints sugar, 'Implicit _' prints as '#', etc *)
val bqual_to_string       : bqual -> string

val args_to_string : args -> string

instance val showable_term      : showable term
instance val showable_univ      : showable universe
instance val showable_comp      : showable comp
instance val showable_sigelt    : showable sigelt
instance val showable_args      : showable args
instance val showable_bv        : showable bv
instance val showable_fv        : showable fv
instance val showable_binder    : showable binder
instance val showable_uvar      : showable uvar
instance val showable_ctxu      : showable ctx_uvar
instance val showable_binding   : showable binding
instance val showable_pragma    : showable pragma
instance val showable_subst_elt : showable subst_elt
instance val showable_branch    : showable branch
instance val showable_aqual     : showable aqual
instance val showable_qualifier : showable qualifier
instance val showable_pat       : showable pat
instance val showable_const     : showable sconst
instance val showable_letbinding : showable letbinding
instance val showable_modul      : showable modul
instance val showable_ctx_uvar_meta : showable ctx_uvar_meta_t
instance val showable_metadata  : showable metadata
instance val showable_cflag     : showable cflag
instance val showable_indexed_effect_combinator_kind : showable indexed_effect_combinator_kind
instance val showable_eff_extraction_mode : showable eff_extraction_mode
instance val showable_sub_eff  : showable sub_eff

instance val pretty_term        : pretty term
instance val pretty_univ        : pretty universe
instance val pretty_comp        : pretty comp
instance val pretty_sigelt      : pretty sigelt
instance val pretty_uvar        : pretty uvar
instance val pretty_ctxu        : pretty ctx_uvar
instance val pretty_binder      : pretty binder
instance val pretty_bv          : pretty bv
instance val pretty_binding     : pretty binding

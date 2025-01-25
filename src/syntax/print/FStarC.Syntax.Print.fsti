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
module FStarC.Syntax.Print

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.Class.Show
open FStarC.Class.PP

module DsEnv = FStarC.Syntax.DsEnv
module Json = FStarC.Json

(* Use the instances if possible! *)

instance val showable_term      : showable term
instance val showable_univ      : showable universe
instance val showable_comp      : showable comp
instance val showable_sigelt    : showable sigelt
instance val showable_bv        : showable bv
instance val showable_fv        : showable fv
instance val showable_binder    : showable binder
instance val showable_uvar      : showable uvar
instance val showable_ctxu      : showable ctx_uvar
instance val showable_binding   : showable binding
instance val showable_subst_elt : showable subst_elt
instance val showable_branch    : showable branch
instance val showable_bqual     : showable binder_qualifier
instance val showable_aqual     : showable aqual
instance val showable_qualifier : showable qualifier
instance val showable_pat       : showable pat
instance val showable_const     : showable sconst
instance val showable_letbinding : showable letbinding
instance val showable_modul      : showable modul
instance val showable_ctx_uvar_meta : showable ctx_uvar_meta_t
instance val showable_metadata  : showable metadata
instance val showable_decreases_order : showable decreases_order
instance val showable_cflag     : showable cflag
instance val showable_sub_eff   : showable sub_eff
instance val showable_eff_decl  : showable eff_decl

instance val pretty_term        : pretty term
instance val pretty_univ        : pretty universe
instance val pretty_comp        : pretty comp
instance val pretty_sigelt      : pretty sigelt
instance val pretty_uvar        : pretty uvar
instance val pretty_ctxu        : pretty ctx_uvar
instance val pretty_binder      : pretty binder
instance val pretty_bv          : pretty bv
instance val pretty_binding     : pretty binding

(* A "short" version of printing a sigelt. Meant to (usually) be a small string
suitable to embed in an error message. No need to be fully faithful to
printing universes, etc, it should just make it clear enough to which
sigelt it refers to. *)
val sigelt_to_string_short: sigelt -> string

(* These versions take in a DsEnv to abbreviate names. *)
val term_to_string'       : DsEnv.env -> term -> string
val comp_to_string'       : DsEnv.env -> comp -> string
val sigelt_to_string'     : DsEnv.env -> sigelt -> string
val term_to_doc'          : DsEnv.env -> term -> Pprint.document
val comp_to_doc'          : DsEnv.env -> comp -> Pprint.document
val sigelt_to_doc'        : DsEnv.env -> sigelt -> Pprint.document

(* Prints as <u1,..,un>ty instead of a pair. *)
val tscheme_to_string : tscheme -> string

(* Prints sugar, 'Implicit _' prints as '#', etc *)
val bqual_to_string       : bqual -> string

(* Prints arguments as they show up in the source, useful
for error messages. *)
val args_to_string : args -> string

(* This should really go elsewhere. *)
val binders_to_json       : DsEnv.env -> binders -> Json.json

val binder_to_string_with_type : binder -> string

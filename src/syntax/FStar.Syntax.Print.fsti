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
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.Const
open FStar.Compiler.Util

module DsEnv = FStar.Syntax.DsEnv
module Json = FStar.Json

val db_to_string          : bv -> string
val bv_to_string          : bv -> string
val bvs_to_string         : string -> list bv -> string
val fv_to_string          : fv -> string
val nm_to_string          : bv -> string
val lid_to_string         : lid -> string
val term_to_string        : term -> string
val term_to_string'       : DsEnv.env -> term -> string
val uvar_to_string        : uvar -> string
val comp_to_string        : comp -> string
val comp_to_string'       : DsEnv.env -> comp -> string
val lbs_to_string         : list qualifier -> letbindings -> string
val tag_of_term           : term -> string
val lbname_to_string      : lbname -> string
val pat_to_string         : pat -> string
val branch_to_string      : Syntax.branch -> string
val modul_to_string       : modul -> string
val univ_names_to_string  : univ_names -> string
val univ_to_string        : universe -> string
val univs_to_string       : universes -> string
val attrs_to_string       : list attribute -> string
val sigelt_to_string      : sigelt -> string
val sigelt_to_string'     : DsEnv.env -> sigelt -> string
val sigelt_to_string_short: sigelt -> string
val tag_of_sigelt         : sigelt -> string
val binder_to_string      : binder -> string
val binders_to_string     : string -> binders -> string
val binder_to_json        : DsEnv.env -> binder -> Json.json
val binders_to_json       : DsEnv.env -> binders -> Json.json
val aqual_to_string       : aqual -> string
val bqual_to_string       : bqual -> string
val args_to_string        : args -> string
val indexed_effect_binder_kind_to_string
                          : indexed_effect_binder_kind -> string
val indexed_effect_combinator_kind_to_string
                          : indexed_effect_combinator_kind -> string
val eff_extraction_mode_to_string
                          : eff_extraction_mode -> string
val eff_decl_to_string    : bool -> eff_decl -> string
val sub_eff_to_string     : sub_eff -> string
val subst_to_string       : subst_t -> string
val const_to_string       : sconst -> string
val qual_to_string        : qualifier -> string
val quals_to_string       : list qualifier -> string
val tscheme_to_string     : tscheme -> string
val cflag_to_string       : cflag -> string
val cflags_to_string      : list cflag -> string
val delta_depth_to_string : delta_depth -> string
val action_to_string  : action -> string
val metadata_to_string : metadata -> string
val ctx_uvar_to_string    : ctx_uvar -> string
val ctx_uvar_to_string_no_reason    : ctx_uvar -> string

val emb_typ_to_string: emb_typ -> string

val fv_qual_to_string : fv_qual -> string

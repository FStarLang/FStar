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
#light "off"
// (c) Microsoft Corporation. All rights reserved

module FStar.Syntax.DsEnv
open FStar.ST
open FStar.All


open FStar
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Util
open FStar.Parser
open FStar.Ident
module BU = FStar.Util
module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util

type used_marker = ref<bool>

type open_kind =                                          (* matters only for resolving names with some module qualifier *)
| Open_module                                             (* only opens the module, not the namespace *)
| Open_namespace                                          (* opens the whole namespace *)

type open_module_or_namespace = (lident * open_kind)      (* lident fully qualified name, already resolved. *)

type record_or_dc = {
  typename: lident; (* the namespace part applies to the constructor and fields as well *)
  constrname: ident;
  parms: binders;
  fields: list<(ident * typ)>;
  is_private: bool;
  is_record:bool
}

type env
type withenv<'a> = env -> 'a * env

type dsenv_hooks =
  { ds_push_open_hook : env -> open_module_or_namespace -> unit;
    ds_push_include_hook : env -> lident -> unit;
    ds_push_module_abbrev_hook : env -> ident -> lident -> unit }

type foundname =
  | Term_name of typ * list<attribute>
  | Eff_name  of sigelt * lident

val fail_or:  env -> (lident -> option<'a>) -> lident -> 'a
val fail_or2: (ident -> option<'a>) -> ident -> 'a

val dep_graph: env -> FStar.Parser.Dep.deps
val set_dep_graph: env -> FStar.Parser.Dep.deps -> env
val ds_hooks : env -> dsenv_hooks
val set_ds_hooks: env -> dsenv_hooks -> env
val syntax_only: env -> bool
val set_syntax_only: env -> bool -> env
val qualify: env -> ident -> lident
val set_iface: env -> bool -> env
val iface: env -> bool
val set_admitted_iface: env -> bool -> env
val admitted_iface: env -> bool
val expect_typ: env -> bool
val set_expect_typ: env -> bool -> env
val empty_env: FStar.Parser.Dep.deps -> env
val current_module: env -> lident
val set_current_module: env -> lident -> env
val open_modules: env -> list<(lident * modul)>
val open_modules_and_namespaces: env -> list<lident>
val iface_decls : env -> lident -> option<(list<Parser.AST.decl>)>
val set_iface_decls: env -> lident -> list<Parser.AST.decl> -> env
val try_lookup_id: env -> ident -> option<term>
val shorten_module_path: env -> list<ident> -> bool -> (list<ident> * list<ident>)
val shorten_lid: env -> lid -> lid
val try_lookup_lid: env -> lident -> option<term>
val try_lookup_lid_with_attributes: env -> lident -> option<(term * list<attribute>)>
val try_lookup_lid_with_attributes_no_resolve: env -> lident -> option<(term * list<attribute>)>
val try_lookup_lid_no_resolve: env -> lident -> option<term>
val try_lookup_effect_name: env -> lident -> option<lident>
val try_lookup_effect_name_and_attributes: env -> lident -> option<(lident * list<cflag>)>
val try_lookup_effect_defn: env -> lident -> option<eff_decl>
(* [try_lookup_root_effect_name] is the same as
[try_lookup_effect_name], but also traverses effect abbrevs. TODO:
once indexed effects are in, also track how indices and other
arguments are instantiated. *)
val try_lookup_root_effect_name: env -> lident -> option<lident>
val try_lookup_datacon: env -> lident -> option<fv>
val try_lookup_record_by_field_name: env -> lident -> option<record_or_dc>
val belongs_to_record: env -> lident -> record_or_dc -> bool
val try_lookup_dc_by_field_name: env -> lident -> option<(lident * bool)>
val try_lookup_definition: env -> lident -> option<term>
val is_effect_name: env -> lident -> bool
val find_all_datacons: env -> lident -> option<list<lident>>
val lookup_letbinding_quals_and_attrs: env -> lident -> list<qualifier> * list<attribute>
val resolve_module_name: env:env -> lid:lident -> honor_ns:bool -> option<lident>
val resolve_to_fully_qualified_name : env:env -> l:lident -> option<lident>
val fv_qual_of_se : sigelt -> option<fv_qual>
val delta_depth_of_declaration: lident -> list<qualifier> -> delta_depth

val push_bv': env -> ident -> env * bv * used_marker
val push_bv: env -> ident -> env * bv
val push_top_level_rec_binding: env -> ident -> S.delta_depth -> env * ref<bool>
val push_sigelt: env -> sigelt -> env
val push_namespace: env -> lident -> env
val push_include: env -> lident -> env
val push_module_abbrev : env -> ident -> lident -> env

(* Won't fail on duplicates, use with caution *)
val push_sigelt_force : env -> sigelt -> env

val pop: unit -> env
val push: env -> env
val rollback: option<int> -> env
val snapshot: env -> (int * env)

val finish_module_or_interface: env -> modul -> (env * modul)
val enter_monad_scope: env -> ident -> env
val export_interface: lident ->  env -> env

val transitive_exported_ids: env -> lident -> list<string>
type module_inclusion_info
val default_mii : module_inclusion_info
val inclusion_info: env -> lident -> module_inclusion_info
val prepare_module_or_interface: bool -> bool -> env -> lident -> module_inclusion_info -> env * bool //pop the context when done desugaring

(* private *) val try_lookup_lid': bool -> bool -> env -> lident -> option<(term * list<attribute>)>
(* private *) val unique:  bool -> bool -> env -> lident -> bool
(* private *) val check_admits: env -> modul -> modul
(* private *) val finish:  env -> modul -> env

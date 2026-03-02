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

module FStarC.Syntax.DsEnv
open FStarC
open FStarC.Effect
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Ident
open FStarC.Class.Show
module S = FStarC.Syntax.Syntax

val ugly_sigelt_to_string_hook : ref (sigelt -> string)

let open_module_or_namespace = S.open_module_or_namespace
type used_marker = ref bool
                                        (* opens the whole namespace *)
type record_or_dc = {
  typename: lident; (* the namespace part applies to the constructor and fields as well *)
  constrname: ident;
  parms: binders;
  fields: list (ident & typ);
  is_private: bool;
  is_record:bool
}

val env : Type0
val dsenv_hooks : Type0

type withenv 'a = env -> 'a & env

type foundname =
  | Term_name of typ & list attribute
  | Eff_name  of sigelt & lident

val parsing_data_for_scope (e:env) : ML (list FStarC.Parser.Dep.parsing_data_elt)
val with_restored_scope (e:env) (f: env -> 'a & env) : ML ('a & env)

instance val showable_env : showable env
val mk_dsenv_hooks
  (open_hook:env -> open_module_or_namespace -> unit)
  (include_hook:env -> lident -> unit)
  (module_abbrev_hook:env -> ident -> lident -> unit)
  : dsenv_hooks

val set_iface: env -> bool -> env
val iface: env -> bool
val set_admitted_iface: env -> bool -> env
val admitted_iface: env -> bool
val set_expect_typ: env -> bool -> env
val expect_typ: env -> bool
val transitive_exported_ids: env -> lident -> ML (list string)
val opens_and_abbrevs :env -> ML (list (either open_module_or_namespace module_abbrev))
val open_modules: env -> list (lident & modul)
val open_modules_and_namespaces: env -> ML (list lident)
val module_abbrevs: env -> ML (list (ident & lident))
val set_current_module: env -> lident -> env
val clear_scope_mods: env -> env
val current_module: env -> ML lident
val iface_decls : env -> lident -> ML (option (list Parser.AST.decl))
val set_iface_decls: env -> lident -> list Parser.AST.decl -> env
val iface_interleaving_init: env -> bool
val qualify: env -> ident -> ML lident
val syntax_only: env -> bool
val set_syntax_only: env -> bool -> env
val ds_hooks : env -> dsenv_hooks
val set_ds_hooks: env -> dsenv_hooks -> env
val empty_env: FStarC.Parser.Dep.deps -> ML env
val dep_graph: env -> FStarC.Parser.Dep.deps
val set_dep_graph: env -> FStarC.Parser.Dep.deps -> env
val try_lookup_id: env -> ident -> ML (option term)
val resolve_module_name: env:env -> lid:lident -> honor_ns:bool -> ML (option lident)
val shorten_module_path: env -> list ident -> bool -> ML (list ident & list ident)
val fv_qual_of_se : sigelt -> ML (option fv_qual)
val try_lookup_effect_name: env -> lident -> ML (option lident)
val try_lookup_effect_name_and_attributes: env -> lident -> ML (option (lident & list cflag))
val try_lookup_effect_defn: env -> lident -> ML (option eff_decl)
val is_effect_name: env -> lident -> ML bool
(* [try_lookup_root_effect_name] is the same as
[try_lookup_effect_name], but also traverses effect abbrevs. TODO:
once indexed effects are in, also track how indices and other
arguments are instantiated. *)
val try_lookup_root_effect_name: env -> lident -> ML (option lident)
val lookup_letbinding_quals_and_attrs: env -> lident -> ML (list qualifier & list attribute)
val try_lookup_definition: env -> lident -> ML (option term)
(* private *) val try_lookup_lid': bool -> bool -> env -> lident -> ML (option (term & list attribute))
val try_lookup_lid_with_attributes: env -> lident -> ML (option (term & list attribute))
val try_lookup_lid: env -> lident -> ML (option term)
val resolve_to_fully_qualified_name : env:env -> l:lident -> ML (option lident)
val shorten_lid: env -> lid -> ML lid
val try_lookup_lid_with_attributes_no_resolve: env -> lident -> ML (option (term & list attribute))
val try_lookup_lid_no_resolve: env -> lident -> ML (option term)
val try_lookup_datacon: env -> lident -> ML (option (fv & sigelt))
val find_all_datacons: env -> lident -> ML (option (list lident))
val try_lookup_record_by_field_name: env -> lident -> ML (option record_or_dc)
(* [try_lookup_record_by_field_name_many] finds a record type that includes all of the given fields *)
val try_lookup_record_by_field_name_many: env -> list lident -> ML (option record_or_dc)
val try_lookup_record_type: env -> lident -> ML (option record_or_dc)
val belongs_to_record: env -> lident -> record_or_dc -> ML bool
val try_lookup_dc_by_field_name: env -> lident -> ML (option (lident & bool))
(* private *) val unique:  bool -> bool -> env -> lident -> ML bool
val push_bv': env -> ident -> ML (env & bv & used_marker)
val push_bv: env -> ident -> ML (env & bv)
val push_top_level_rec_binding: env -> ident -> ML (env & ref bool)
val push_sigelt: env -> sigelt -> ML env
(* Won't fail on duplicates, use with caution *)
val push_sigelt_force : env -> sigelt -> ML env
val push_namespace: env -> lident -> restriction -> ML env
val push_include: env -> lident -> restriction -> ML env
val push_module_abbrev : env -> ident -> lident -> ML env
(* private *) val check_admits: env -> modul -> ML modul
(* private *) val finish:  env -> modul -> ML env
val push: env -> ML env
val pop: unit -> ML env
val snapshot: env -> ML (int & env)
val rollback: option int -> ML env
val export_interface: lident ->  env -> ML env
val finish_module_or_interface: env -> modul -> ML (env & modul)
val module_inclusion_info : Type0
instance val showable_mii: showable module_inclusion_info
val default_mii : module_inclusion_info
val inclusion_info: env -> lident -> ML module_inclusion_info
val prepare_module_or_interface: no_prelude:bool -> is_interface:bool -> is_admitted:bool -> env -> lident -> module_inclusion_info -> ML (env & bool) //pop the context when done desugaring
val enter_monad_scope: env -> ident -> ML env
val fail_or:  env -> (lident -> option 'a) -> lident -> ML 'a
val fail_or2: env -> (ident -> option 'a) -> ident -> ML 'a
val resolve_name: env -> lident -> ML (option (either bv fv))
val set_no_prelude : env -> bool -> env

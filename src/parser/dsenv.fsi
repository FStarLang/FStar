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

module FStar.Parser.DesugarEnv


open FStar
open FStar.Util
open FStar.Absyn
open FStar.Absyn.Syntax
open FStar.Absyn.Util
open FStar.Absyn.Const
open FStar.Parser

type binding =
  | Binding_typ_var of ident
  | Binding_var of ident
  | Binding_let of lident
  | Binding_tycon of lident

type kind_abbrev = lident * list<either<btvdef, bvvdef>> * Syntax.knd
type env = {
  curmodule: option<lident>;
  modules:list<(lident * modul)>;  (* previously desugared modules *)
  open_namespaces: list<lident>; (* fully qualified names, in order of precedence *)
  sigaccum:sigelts;              (* type declarations being accumulated for the current module *)
  localbindings:list<(either<btvdef,bvvdef> * binding)>;  (* local name bindings for name resolution, paired with an env-generated unique name *)
  recbindings:list<binding>;     (* names bound by recursive type and top-level let-bindings definitions only *)
  phase:AST.level;
  sigmap: list<Util.smap<(sigelt * bool)>>; (* bool indicates that this was declared in an interface file *)
  default_result_effect:typ -> Range.range -> comp;
  iface:bool;
  admitted_iface:bool
}

type record_or_dc = {
  typename: lident;
  constrname: lident;
  parms: binders;
  fields: list<(fieldname * typ)>;
  is_record:bool
}

val fail_or:  env -> (lident -> option<'a>) -> lident -> 'a
val fail_or2: (ident -> option<'a>) -> ident -> 'a

val qualify: env -> ident -> lident
val qualify_lid: env -> lident -> lident

val empty_env: unit -> env
val default_total: env -> env
val default_ml: env -> env
type occurrence =
  | OSig of sigelt
  | OLet of lident
  | ORec of lident
type foundname =
  | Exp_name of occurrence * exp
  | Typ_name of occurrence * typ
  | Eff_name of occurrence * lident
  | Knd_name of occurrence * lident
val current_module: env -> lident
val try_lookup_name : bool -> bool -> env -> lident -> option<foundname>
val try_lookup_typ_var: env -> ident -> option<typ>
val resolve_in_open_namespaces: env -> lident -> (lident -> option<'a>) -> option<'a>
val try_lookup_typ_name: env -> lident -> option<typ>
val is_effect_name: env -> lident -> bool
val try_lookup_effect_name: env -> lident -> option<lident>
val try_lookup_effect_defn: env -> lident -> option<eff_decl>
val try_resolve_typ_abbrev: env -> lident -> option<typ>
val try_lookup_id: env -> ident -> option<exp>
val try_lookup_lid: env -> lident -> option<exp>
val try_lookup_datacon: env -> lident -> option<var<typ>>
val try_lookup_record_by_field_name: env -> lident -> option<(record_or_dc * lident)>
val try_lookup_projector_by_field_name: env -> lident -> option<(lident * bool)>

val qualify_field_to_record: env -> record_or_dc -> lident -> option<lident>
val find_kind_abbrev: env -> lident -> option<lident>
val is_kind_abbrev: env -> lident -> bool
val push_bvvdef: env -> bvvdef -> env
val push_btvdef: env -> btvdef -> env
val push_local_binding: env -> binding -> env * either<btvdef, bvvdef>
val push_local_vbinding: env -> ident -> env * bvvdef
val push_local_tbinding: env -> ident -> env * btvdef
val push_rec_binding: env -> binding -> env
val push_sigelt: env -> sigelt -> env
val push_namespace: env -> lident -> env
val is_type_lid: env -> lident -> bool
val find_all_datacons: env -> lident -> option<list<lident>>
val lookup_letbinding_quals: env -> lident -> list<qualifier>

val pop: env -> env
val push: env -> env
val mark: env -> env
val reset_mark: env -> env
val commit_mark: env -> env
val finish_module_or_interface: env -> modul -> env
val prepare_module_or_interface: bool -> bool -> env -> lident -> env * bool //pop the context when done desugaring
val enter_monad_scope: env -> ident -> env
val exit_monad_scope: env -> env -> env
val export_interface: lident ->  env -> env

(* private *) val unmangleOpName: ident -> option<lident>
(* private *) val try_lookup_lid': bool -> bool -> env -> lident -> option<exp>
(* private *) val extract_record: env -> sigelt -> unit
(* private *) val unique_name: bool -> bool -> env -> lident -> bool
(* private *) val unique_typ_name: env -> lident -> bool
(* private *) val unique:  bool -> bool -> env -> lident -> bool
(* private *) val check_admits:  lident -> env -> unit
(* private *) val finish:  env -> modul -> env

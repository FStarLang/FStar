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

module FStar.Parser.Env


open FStar
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Util
open FStar.Syntax.Const
open FStar.Parser
open FStar.Ident

module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util

type local_binding = (ident * bv * bool)                  (* local name binding for name resolution, paired with an env-generated unique name and a boolean that is true when the variable has been introduced with let-mutable *)
type rec_binding   = (ident * lid * delta_depth)          (* name bound by recursive type and top-level let-bindings definitions only *)
type module_abbrev = (ident * lident)                     (* module X = A.B.C *)

type open_kind =                                          (* matters only for resolving names with some module qualifier *)
| Open_module                                             (* only opens the module, not the namespace *)
| Open_namespace                                          (* opens the whole namespace *)

type open_module_or_namespace = (lident * open_kind)      (* lident fully qualified name, already resolved. *)

type record_or_dc = {
  typename: lident;
  constrname: lident;
  parms: binders;
  fields: list<(fieldname * typ)>;
  is_record:bool
}

type scope_mod =
| Local_binding            of local_binding
| Rec_binding              of rec_binding
| Module_abbrev            of module_abbrev
| Open_module_or_namespace of open_module_or_namespace
| Top_level_def            of ident           (* top-level definition for an unqualified identifier x to be resolved as curmodule.x. *)
| Record_or_dc             of record_or_dc    (* to honor interleavings of "open" and record definitions *)

type env = {
  curmodule:            option<lident>;                   (* name of the module being desugared *)
  curmonad:             option<ident>;                    (* current monad being desugared *)
  modules:              list<(lident * modul)>;           (* previously desugared modules *)
  scope_mods:           list<scope_mod>;                  (* toplevel or definition-local scope modifiers *)
  sigaccum:             sigelts;                          (* type declarations being accumulated for the current module *)
  sigmap:               Util.smap<(sigelt * bool)>;       (* bool indicates that this was declared in an interface file *)
  default_result_effect:lident;                           (* either Tot or ML, depending on the what kind of term we're desugaring *)
  iface:                bool;                             (* remove? whether or not we're desugaring an interface; different scoping rules apply *)
  admitted_iface:       bool;                             (* is it an admitted interface; different scoping rules apply *)
  expect_typ:           bool;                             (* syntactically, expect a type at this position in the term *)
}

type foundname =
  | Term_name of typ * bool // indicates if mutable
  | Eff_name  of sigelt * lident

val fail_or:  env -> (lident -> option<'a>) -> lident -> 'a
val fail_or2: (ident -> option<'a>) -> ident -> 'a

val qualify: env -> ident -> lident

val empty_env: unit -> env
val default_total: env -> env
val default_ml: env -> env

val current_module: env -> lident
val try_lookup_id: env -> ident -> option<(term*bool)>
val try_lookup_lid: env -> lident -> option<(term*bool)>
val try_lookup_effect_name: env -> lident -> option<lident>
val try_lookup_effect_defn: env -> lident -> option<eff_decl>
val try_lookup_datacon: env -> lident -> option<fv>
val try_lookup_record_by_field_name: env -> lident -> option<(record_or_dc * lident)>
val belongs_to_record: env -> lident -> record_or_dc -> bool
val try_lookup_projector_by_field_name: env -> lident -> option<(lident * bool)>
val try_lookup_definition: env -> lident -> option<term>
val is_effect_name: env -> lident -> bool
val find_all_datacons: env -> lident -> option<list<lident>>
val lookup_letbinding_quals: env -> lident -> list<qualifier>
val qualify_field_to_record: env -> record_or_dc -> lident -> option<lident>

val push_bv: env -> ident -> env * bv
val push_bv_mutable: env -> ident -> env * bv
val push_top_level_rec_binding: env -> ident -> S.delta_depth -> env
val push_sigelt: env -> sigelt -> env
val push_namespace: env -> lident -> env
val push_module_abbrev : env -> ident -> lident -> env

val pop: env -> env
val push: env -> env
val mark: env -> env
val reset_mark: env -> env
val commit_mark: env -> env
val finish_module_or_interface: env -> modul -> env
val prepare_module_or_interface: bool -> bool -> env -> lident -> env * bool //pop the context when done desugaring
val enter_monad_scope: env -> ident -> env
val export_interface: lident ->  env -> env

(* private *) val try_lookup_lid': bool -> bool -> env -> lident -> option<(term*bool)>
(* private *) val unique:  bool -> bool -> env -> lident -> bool
(* private *) val check_admits: env -> unit
(* private *) val finish:  env -> modul -> env

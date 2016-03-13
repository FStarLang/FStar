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

type env = {
  curmodule:            option<lident>;                   (* name of the module being desugared *)
  modules:              list<(lident * modul)>;           (* previously desugared modules *)
  open_namespaces:      list<lident>;                     (* fully qualified names, in order of precedence *)
  sigaccum:             sigelts;                          (* type declarations being accumulated for the current module *)
  localbindings:        list<(ident * bv)>;               (* local name bindings for name resolution, paired with an env-generated unique name *)
  recbindings:          list<(ident*lid*delta_depth)>;    (* names bound by recursive type and top-level let-bindings definitions only *)
  sigmap:               list<Util.smap<(sigelt * bool)>>; (* bool indicates that this was declared in an interface file *)
  default_result_effect:lident;                           (* either Tot or ML, depending on the what kind of term we're desugaring *)
  iface:                bool;                             (* remove? whether or not we're desugaring an interface; different scoping rules apply *)
  admitted_iface:       bool;                             (* is it an admitted interface; different scoping rules apply *)
  expect_typ:           bool;                             (* syntatically, expect a type at this position in the term *)
}

type record_or_dc = {
  typename: lident;
  constrname: lident;
  parms: binders;
  fields: list<(fieldname * typ)>;
  is_record:bool
}
type foundname =
  | Term_name of term
  | Eff_name  of sigelt * lident

val fail_or:  (lident -> option<'a>) -> lident -> 'a
val fail_or2: (ident -> option<'a>) -> ident -> 'a

val qualify: env -> ident -> lident
val qualify_lid: env -> lident -> lident

val empty_env: unit -> env
val default_total: env -> env
val default_ml: env -> env

val current_module: env -> lident
val try_lookup_id: env -> ident -> option<term>
val try_lookup_lid: env -> lident -> option<term>
val try_lookup_effect_name: env -> lident -> option<lident>
val try_lookup_effect_defn: env -> lident -> option<eff_decl>
val try_lookup_datacon: env -> lident -> option<fv>
val try_lookup_record_by_field_name: env -> lident -> option<(record_or_dc * lident)>
val try_lookup_projector_by_field_name: env -> lident -> option<(lident * bool)>
val try_lookup_definition: env -> lident -> option<term>
val is_effect_name: env -> lident -> bool
val find_all_datacons: env -> lident -> option<list<lident>>
val lookup_letbinding_quals: env -> lident -> list<qualifier>
val qualify_field_to_record: env -> record_or_dc -> lident -> option<lident>

val push_bv: env -> ident -> env * bv
val push_top_level_rec_binding: env -> ident -> S.delta_depth -> env
val push_sigelt: env -> sigelt -> env
val push_namespace: env -> lident -> env

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

(* private *) val try_lookup_lid': bool -> bool -> env -> lident -> option<term>
(* private *) val extract_record: env -> sigelt -> unit
(* private *) val unique:  bool -> bool -> env -> lident -> bool
(* private *) val check_admits: env -> unit
(* private *) val finish:  env -> modul -> env
(* private *) val resolve_in_open_namespaces: env -> lident -> (lident -> option<'a>) -> option<'a>

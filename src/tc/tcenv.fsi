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
// (c) Microsoft Corporation. All rights reserved

module FStar.Tc.Env

open FStar
open FStar.Absyn.Syntax


type binding =
  | Binding_var of bvvdef * typ
  | Binding_typ of btvdef * knd
  | Binding_lid of lident * typ
  | Binding_sig of sigelt

type level =
  | Expr
  | Type
  | Kind

type mlift = typ -> typ -> typ
type edge = {
  msource:lident;
  mtarget:lident;
  mlift:typ -> typ -> typ;
}
type effects = {
  decls: list<eff_decl>;
  order: list<edge>;                                     (* transitive closure of the order in the signature *)
  joins: list<(lident * lident * lident * mlift * mlift)>; (* least upper bounds *)
}

type env = {
  solver: solver_t;              (* interface to the SMT solver *)
  range:Range.range;             (* the source location of the term being checked *)
  curmodule: lident;             (* Name of this module *)
  gamma:list<binding>;           (* Local typing environment and signature elements *)
  modules:list<modul>;           (* already fully type checked modules *)
  expected_typ:option<typ>;      (* type expected by the context *)
  level:level;                   (* current term being checked is at level *)
  sigtab:list<Util.smap<sigelt>>; (* a dictionary of long-names to sigelts *)
  is_pattern:bool;                (* is the current term being checked a pattern? *)
  instantiate_targs:bool;         (* instantiate implicit type arguments? default=true *)
  instantiate_vargs:bool;        (* instantiate implicit term arguments? default=true *)
  effects:effects;               (* monad lattice *)
  generalize:bool;               (* should we generalize let bindings? *)
  letrecs:list<(lbname * typ)>;  (* mutually recursive names and their types (for termination checking) *)
  top_level:bool;                (* is this a top-level term? if so, then discharge guards *)
  check_uvars:bool;              (* paranoid: re-typecheck unification variables *)
  use_eq:bool;                   (* generate an equality constraint, rather than subtyping/subkinding *)
  is_iface:bool;                 (* is the module we're currently checking an interface? *)
  admit:bool;                    (* admit VCs in the current module *)
  default_effects:list<(lident*lident)>;
}
and solver_t = {
    init: env -> unit;
    push: string -> unit;
    pop: string -> unit;
    mark: string -> unit;
    reset_mark: string -> unit;
    commit_mark: string -> unit;
    encode_modul:env -> modul -> unit;
    encode_sig:env -> sigelt -> unit;
    solve:env -> typ -> unit;// (bool * list<string>);
    is_trivial: env -> typ -> bool;
    finish:  unit -> unit;
    refresh: unit -> unit;
}
val push: env -> string -> env
val pop: env -> string -> env
val mark: env -> env
val reset_mark: env -> env
val commit_mark: env -> env
val bound_vars: env -> list<Util.either<btvar, bvvar>>
val debug: env -> Options.debug_level_t -> bool
val show: env -> bool
val initial_env : solver_t -> lident -> env
val finish_module : env -> modul -> env
val set_level : env -> level -> env
val is_level : env -> level -> bool
val modules : env -> list<modul>
val current_module : env -> lident
val set_current_module : env -> lident -> env
val set_range : env -> Range.range -> env
val get_range : env -> Range.range

val default_effect : env -> lident -> option<lident>
val lookup_bvar : env -> bvvar -> typ
val lookup_lid : env -> lident -> typ
val lookup_kind_abbrev: env -> lident -> (lident * binders * knd)
val try_lookup_val_decl : env -> lident -> option<(typ * list<qualifier>)>
val lookup_val_decl : env -> lident -> typ
val lookup_datacon: env -> lident -> typ
val is_datacon : env -> lident -> bool
val is_record : env -> lident -> bool
val lookup_datacons_of_typ : env -> lident -> option<list<(lident * typ)>>
val lookup_typ_abbrev : env -> lident -> option<typ>
val lookup_opaque_typ_abbrev: env -> lident -> option<typ>
val lookup_effect_abbrev : env -> lident -> option<(binders * comp)>
val lookup_btvar : env -> btvar -> knd
val lookup_typ_lid : env -> lident -> knd
val is_projector: env -> lident -> bool
val try_lookup_effect_lid : env -> lident -> option<knd>
val lookup_effect_lid : env -> lident -> knd
val lookup_operator : env -> ident -> typ
val lookup_projector: env -> lident -> int -> lident
val lookup_qname: env -> lident -> option<Util.either<typ,sigelt>>

val push_sigelt : env -> sigelt -> env
val push_local_binding : env -> binding -> env
val uvars_in_env : env -> uvars
val push_module : env -> modul -> env

val set_expected_typ : env -> typ -> env
val expected_typ : env -> option<typ>
val clear_expected_typ : env -> env*option<typ>

val fold_env : env -> ('a -> binding -> 'a) -> 'a -> 'a
val binding_of_binder: binder -> binding
val idents : env -> freevars
val binders: env -> binders
val t_binders : env -> FStar.Absyn.Syntax.binders
val lidents : env -> list<lident>

(* operations on monads *)
val join: env -> lident -> lident -> lident * mlift * mlift
val monad_leq: env -> lident -> lident -> option<edge>
val effect_decl_opt: env -> lident -> option<eff_decl>
val get_effect_decl: env -> lident -> eff_decl
val wp_signature: env -> lident -> (btvar * knd)

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
module FStar.TypeChecker.Env
open FStar
open FStar.Syntax.Syntax
open FStar.Ident

type binding =
  | Binding_var of bv     * tscheme
  | Binding_lid of lident * tscheme
  | Binding_sig of sigelt

type mlift = typ -> typ -> typ

type edge = {
  msource :lident;
  mtarget :lident;
  mlift   :typ -> typ -> typ;
}
type effects = {
  decls :list<eff_decl>;
  order :list<edge>;                                       (* transitive closure of the order in the signature *)
  joins :list<(lident * lident * lident * mlift * mlift)>; (* least upper bounds *)
}

type env = {
  solver         :solver_t;                (* interface to the SMT solver *)
  range          :Range.range;             (* the source location of the term being checked *)
  curmodule      :lident;                  (* Name of this module *)
  gamma          :list<binding>;           (* Local typing environment and signature elements *)
  modules        :list<modul>;             (* already fully type checked modules *)
  expected_typ   :option<typ>;             (* type expected by the context *)
  sigtab         :list<Util.smap<sigelt>>; (* a dictionary of long-names to sigelts *)
  is_pattern     :bool;                    (* is the current term being checked a pattern? *)
  instantiate_imp:bool;                    (* instantiate implicit arguments? default=true *)
  effects        :effects;                 (* monad lattice *)
  generalize     :bool;                    (* should we generalize let bindings? *)
  letrecs        :list<(lbname * typ)>;    (* mutually recursive names and their types (for termination checking) *)
  top_level      :bool;                    (* is this a top-level term? if so, then discharge guards *)
  check_uvars    :bool;                    (* paranoid: re-typecheck unification variables *)
  use_eq         :bool;                    (* generate an equality constraint, rather than subtyping/subkinding *)
  is_iface       :bool;                    (* is the module we're currently checking an interface? *)
  admit          :bool;                    (* admit VCs in the current module *)
  default_effects:list<(lident*lident)>;   (* [(x,y)] ... y is the default effect of x *)
}
and solver_t = {
    init         :env -> unit;
    push         :string -> unit;
    pop          :string -> unit;
    mark         :string -> unit;
    reset_mark   :string -> unit;
    commit_mark  :string -> unit;
    encode_modul :env -> modul -> unit;
    encode_sig   :env -> sigelt -> unit;
    solve        :env -> typ -> unit;
    is_trivial   :env -> typ -> bool;
    finish       :unit -> unit;
    refresh      :unit -> unit;
}

val initial_env : solver_t -> lident -> env

(* Marking and resetting the environment, for the interactive mode *)
val push        : env -> string -> env
val pop         : env -> string -> env
val mark        : env -> env
val reset_mark  : env -> env
val commit_mark : env -> env

(* Checking the per-module debug level and position info *)
val debug     : env -> Options.debug_level_t -> bool
val set_range : env -> Range.range -> env
val get_range : env -> Range.range

(* Querying identifiers *)
val lookup_bv              : env -> bv -> typ
val lookup_lid             : env -> lident -> typ
val try_lookup_val_decl    : env -> lident -> option<(tscheme * list<qualifier>)>
val lookup_val_decl        : env -> lident -> typ
val lookup_datacon         : env -> lident -> typ
val lookup_datacons_of_typ : env -> lident -> option<list<(lident * typ)>>
val lookup_definition      : env -> lident -> option<term>
val try_lookup_effect_lid  : env -> lident -> option<term>
val lookup_effect_lid      : env -> lident -> term
val lookup_effect_abbrev   : env -> lident -> option<(binders * comp)>
val lookup_projector       : env -> lident -> int -> lident
val current_module         : env -> lident
val is_projector           : env -> lident -> bool
val is_datacon             : env -> lident -> bool
val is_record              : env -> lident -> bool
val uinst                  : env -> tscheme -> term

(* Introducing identifiers and updating the environment *)
val push_sigelt        : env -> sigelt -> env
val push_local_binding : env -> binding -> env
val push_module        : env -> modul -> env
val push_univ_vars     : env -> univ_names -> env
val set_expected_typ   : env -> typ -> env
val expected_typ       : env -> option<typ>
val clear_expected_typ : env -> env*option<typ>
val set_current_module : env -> lident -> env
val finish_module      : (env -> modul -> env)

(* Collective state of the environment *)
val bound_vars   : env -> list<bv>
val binders      : env -> binders
val modules      : env -> list<modul>
val uvars_in_env : env -> uvars
val univ_vars    : env -> Util.set<universe_uvar>
val lidents      : env -> list<lident>
val fold_env     : env -> ('a -> binding -> 'a) -> 'a -> 'a

(* operations on monads *)
val default_effect  : env -> lident -> option<lident>
val join            : env -> lident -> lident -> lident * mlift * mlift
val monad_leq       : env -> lident -> lident -> option<edge>
val effect_decl_opt : env -> lident -> option<eff_decl>
val get_effect_decl : env -> lident -> eff_decl
val wp_signature    : env -> lident -> (bv * term)

(* A coercion *)
val binders_of_bindings : list<binding> -> binders

(* TODO: REMOVE *)
val dummy:env

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
module FStar.TypeChecker.Env
open FStar.All
open FStar
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.TypeChecker.Common
module BU = FStar.Util

type binding =
  | Binding_var      of bv
  | Binding_lid      of lident * tscheme
  | Binding_sig      of list<lident> * sigelt
  | Binding_univ     of univ_name
  | Binding_sig_inst of list<lident> * sigelt * universes //the first component should always be a Sig_inductive

type delta_level =
  | NoDelta
  | Inlining
  | Eager_unfolding_only
  | Unfold of delta_depth

(* Type of wp liftings [l] between 2 effects Msource and Mtarget : *)
(* given a computational type [Msource t wp], [wp' = mlift_wp t wp] should *)
(* be a weakest precondition such that [Mtarget t wp'] is well-formed *)
(* and if both effects are reifiable, [mlift_term], if provided, maps *)
(* computations [e] of type [Msource.repr t wp] to a computation of type *)
(* [Mtarget.repr t (lift_wp t wp)] *)
type mlift = {
  mlift_wp:typ -> typ -> typ ;
  mlift_term:option<(typ -> typ -> term -> term)>
  (* KM : not exactly sure if mlift_term really need the wp term inside the compiler *)
  (* (it needs it in the F* source to be well-typed but we are forgetting a lot here) *)
}

(* Edge in the effect lattice *)
type edge = {
  msource :lident;
  mtarget :lident;
  mlift   :mlift;
}


type effects = {
  decls :list<eff_decl>;
  order :list<edge>;                                       (* transitive closure of the order in the signature *)
  joins :list<(lident * lident * lident * mlift * mlift)>; (* least upper bounds *)
}

type cached_elt = FStar.Util.either<(universes * typ), (sigelt * option<universes>)> * Range.range
type goal = term
type env = {
  solver         :solver_t;                     (* interface to the SMT solver *)
  range          :Range.range;                  (* the source location of the term being checked *)
  curmodule      :lident;                       (* Name of this module *)
  gamma          :list<binding>;                (* Local typing environment and signature elements *)
  gamma_cache    :FStar.Util.smap<cached_elt>;  (* Memo table for the local environment *)
  modules        :list<modul>;                  (* already fully type checked modules *)
  expected_typ   :option<typ>;                  (* type expected by the context *)
  sigtab         :FStar.Util.smap<sigelt>;      (* a dictionary of long-names to sigelts *)
  is_pattern     :bool;                         (* is the current term being checked a pattern? *)
  instantiate_imp:bool;                         (* instantiate implicit arguments? default=true *)
  effects        :effects;                      (* monad lattice *)
  generalize     :bool;                         (* should we generalize let bindings? *)
  letrecs        :list<(lbname * typ)>;         (* mutually recursive names and their types (for termination checking) *)
  top_level      :bool;                         (* is this a top-level term? if so, then discharge guards *)
  check_uvars    :bool;                         (* paranoid: re-typecheck unification variables *)
  use_eq         :bool;                         (* generate an equality constraint, rather than subtyping/subkinding *)
  is_iface       :bool;                         (* is the module we're currently checking an interface? *)
  admit          :bool;                         (* admit VCs in the current module *)
  lax            :bool;                         (* don't even generate VCs *)
  lax_universes  :bool;                         (* don't check universe constraints *)
  type_of        :env -> term ->term*typ*guard_t; (* a callback to the type-checker; check_term g e = t ==> g |- e : Tot t *)
  universe_of    :env -> term -> universe;        (* a callback to the type-checker; g |- e : Tot (Type u) *)
  use_bv_sorts   :bool;                           (* use bv.sort for a bound-variable's type rather than consulting gamma *)
  qname_and_index:option<(lident*int)>;           (* the top-level term we're currently processing and the nth query for it *)
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
    preprocess   :env -> goal -> list<(env * goal)>;  //a hook for a tactic; still too simple
    solve        :option<(unit -> string)> -> env -> goal -> unit; //call to the smt solver
    is_trivial   :env -> goal -> bool;
    finish       :unit -> unit;
    refresh      :unit -> unit;
}
and guard_t = {
  guard_f:    guard_formula;
  deferred:   deferred;
  univ_ineqs: list<universe> * list<univ_ineq>;
  implicits:  implicits;
}
and implicits = list<(string * env * uvar * term * typ * Range.range)>

type env_t = env
val initial_env : (env -> term -> term*typ*guard_t) -> (env -> term -> universe) -> solver_t -> lident -> env

(* Some utilities *)
val should_verify   : env -> bool
val incr_query_index: env -> env

(* Marking and resetting the environment, for the interactive mode *)
val push               : env -> string -> env
val pop                : env -> string -> env
val mark               : env -> env
val reset_mark         : env -> env
val commit_mark        : env -> env
val cleanup_interactive: env -> unit

(* Checking the per-module debug level and position info *)
val debug          : env -> Options.debug_level_t -> bool
val current_module : env -> lident
val set_range      : env -> Range.range -> env
val get_range      : env -> Range.range

(* Querying identifiers *)
val lid_exists             : env -> lident -> bool
val try_lookup_bv          : env -> bv -> option<(typ * Range.range)>
val lookup_bv              : env -> bv -> typ * Range.range
val try_lookup_lid         : env -> lident -> option<((universes * typ) * (Range.range * option<fsdoc>))>
val lookup_lid             : env -> lident -> (universes * typ) * (Range.range * option<fsdoc>)
val lookup_univ            : env -> univ_name -> bool
val try_lookup_val_decl    : env -> lident -> option<(tscheme * list<qualifier>)>
val lookup_val_decl        : env -> lident -> (universes * typ)
val lookup_datacon         : env -> lident -> universes * typ
(* the boolean tells if the lident was actually a inductive *)
val datacons_of_typ        : env -> lident -> (bool * list<lident>)
val typ_of_datacon         : env -> lident -> lident
val lookup_definition      : list<delta_level> -> env -> lident -> option<(univ_names * term)>
val try_lookup_effect_lid  : env -> lident -> option<term>
val lookup_effect_lid      : env -> lident -> term
val lookup_effect_abbrev   : env -> universes -> lident -> option<(binders * comp)>
val norm_eff_name          : (env -> lident -> lident)
val lookup_effect_quals    : env -> lident -> list<qualifier>
val lookup_projector       : env -> lident -> int -> lident
val is_projector           : env -> lident -> bool
val is_datacon             : env -> lident -> bool
val is_record              : env -> lident -> bool
val is_action              : env -> lident -> bool
val is_interpreted         : (env -> term -> bool)
val is_type_constructor    : env -> lident -> bool
val num_inductive_ty_params: env -> lident -> int

(* Universe instantiation *)

(* Construct a new universe unification variable *)
val new_u_univ             : unit -> universe
(* Instantiate the universe variables in a type scheme with new unification variables *)
val inst_tscheme           : tscheme -> universes * term
val inst_effect_fun_with   : universes -> env -> eff_decl -> tscheme -> term


(* Introducing identifiers and updating the environment *)
val push_sigelt        : env -> sigelt -> env
val push_sigelt_inst   : env -> sigelt -> universes -> env
val push_bv            : env -> bv -> env
val pop_bv             : env -> option<(bv * env)>
val push_let_binding   : env -> lbname -> tscheme -> env
val push_binders       : env -> binders -> env
val push_module        : env -> modul -> env
val push_univ_vars     : env -> univ_names -> env
val set_expected_typ   : env -> typ -> env
val expected_typ       : env -> option<typ>
val clear_expected_typ : env -> env*option<typ>
val set_current_module : env -> lident -> env
val finish_module      : (env -> modul -> env)
val eq_gamma           : env -> env -> bool

(* Collective state of the environment *)
val bound_vars   : env -> list<bv>
val all_binders  : env -> binders
val modules      : env -> list<modul>
val uvars_in_env : env -> uvars
val univ_vars    : env -> FStar.Util.set<universe_uvar>
val univnames   : env -> FStar.Util.set<univ_name>
val lidents      : env -> list<lident>
val fold_env     : env -> ('a -> binding -> 'a) -> 'a -> 'a

(* operations on monads *)
val identity_mlift      : mlift
val join                : env -> lident -> lident -> lident * mlift * mlift
val monad_leq           : env -> lident -> lident -> option<edge>
val effect_decl_opt     : env -> lident -> option<eff_decl>
val get_effect_decl     : env -> lident -> eff_decl
val wp_signature        : env -> lident -> (bv * term)
val null_wp_for_eff     : env -> lident -> universe -> term -> comp
val comp_to_comp_typ    : env -> comp -> comp_typ
val unfold_effect_abbrev: env -> comp -> comp_typ
val effect_repr         : env -> comp -> universe -> option<term>
val reify_comp          : env -> comp -> universe -> term
(* [is_reifiable_* env x] returns true if the effect name/computational effect (of *)
(* a body or codomain of an arrow) [x] is reifiable *)
val is_reifiable_effect : env -> lident -> bool
val is_reifiable : env -> BU.either<lcomp, residual_comp> -> bool
val is_reifiable_comp : env -> comp -> bool
val is_reifiable_function : env -> term -> bool


(* A coercion *)
val binders_of_bindings : list<binding> -> binders

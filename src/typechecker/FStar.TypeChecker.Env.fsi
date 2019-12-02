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
open FStar.ST
open FStar.All
open FStar
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.TypeChecker.Common

module BU = FStar.Util
module S = FStar.Syntax.Syntax
module TcComm = FStar.TypeChecker.Common

type step =
  | Beta
  | Iota            //pattern matching
  | Zeta            //fixed points
  | Exclude of step //the first three kinds are included by default, unless Excluded explicity
  | Weak            //Do not descend into binders
  | HNF             //Only produce a head normal form
  | Primops         //reduce primitive operators like +, -, *, /, etc.
  | Eager_unfolding
  | Inlining
  | DoNotUnfoldPureLets
  | UnfoldUntil of delta_depth
  | UnfoldOnly  of list<FStar.Ident.lid>
  | UnfoldFully of list<FStar.Ident.lid>
  | UnfoldAttr  of list<FStar.Ident.lid>
  | UnfoldTac
  | PureSubtermsWithinComputations
  | Simplify        //Simplifies some basic logical tautologies: not part of definitional equality!
  | EraseUniverses
  | AllowUnboundUniverses //we erase universes as we encode to SMT; so, sometimes when printing, it's ok to have some unbound universe variables
  | Reify
  | CompressUvars
  | NoFullNorm
  | CheckNoUvars
  | Unmeta          //remove all non-monadic metas.
  | Unascribe
  | NBE
  | ForExtraction   //marking an invocation of the normalizer for extraction
and steps = list<step>

val eq_step : step -> step -> bool

type sig_binding = list<lident> * sigelt

type delta_level =
  | NoDelta
  | InliningDelta // ZP : Trying to resolve name clash
  | Eager_unfolding_only
  | Unfold of delta_depth

// A name prefix, such as ["FStar";"Math"]
type name_prefix = FStar.Ident.path
// A choice of which name prefixes are enabled/disabled
// The leftmost match takes precedence. Empty list means everything is off.
// To turn off everything, one can prepend `([], false)` to this (since [] is a prefix of everything)
type proof_namespace = list<(name_prefix * bool)>

type cached_elt = FStar.Util.either<(universes * typ), (sigelt * option<universes>)> * Range.range
type goal = term


(*
 * AR: The mlift record that maintains functions to lift 'source' computation types
 *     and terms to 'target' computation types and terms (terms in the case of reifiable effects)
 *
 *     The signature to lift computation types is quite nice: comp to comp
 *     For the terms, we don't require the indices (wps etc.) anymore since
 *     they are computationally irrelevant, in the previous code where we needed them
 *     all the clients were passing Tm_unknown, so what's the point
 *     Read the signature as: u_a:universe -> a:typ -> e:term -> term
 *
 *     Note that these types compose quite nicely along the effect lattice
 *)

type lift_comp_t = env -> comp -> comp * guard_t

and mlift = {
  mlift_wp:lift_comp_t;
  mlift_term:option<(universe -> typ -> term -> term)>
}

(* Edge in the effect lattice *)
and edge = {
  msource :lident;
  mtarget :lident;
  mlift   :mlift;
}

and effects = {
  decls :list<(eff_decl * list<qualifier>)>;
  order :list<edge>;                                       (* transitive closure of the order in the signature *)
  joins :list<(lident * lident * lident * mlift * mlift)>; (* least upper bounds *)
}

and env = {
  solver         :solver_t;                     (* interface to the SMT solver *)
  range          :Range.range;                  (* the source location of the term being checked *)
  curmodule      :lident;                       (* Name of this module *)
  gamma          :list<binding>;                (* Local typing environment *)
  gamma_sig      :list<sig_binding>;            (* and signature elements *)
  gamma_cache    :FStar.Util.smap<cached_elt>;  (* Memo table for the local environment *)
  modules        :list<modul>;                  (* already fully type checked modules *)
  expected_typ   :option<typ>;                  (* type expected by the context *)
  sigtab         :BU.smap<sigelt>;              (* a dictionary of long-names to sigelts *)
  attrtab        :BU.smap<list<sigelt>>;        (* a dictionary of attribute( name)s to sigelts, mostly in support of typeclasses *)
  instantiate_imp:bool;                         (* instantiate implicit arguments? default=true *)
  effects        :effects;                      (* monad lattice *)
  generalize     :bool;                         (* should we generalize let bindings? *)
  letrecs        :list<(lbname * typ * univ_names)>;           (* mutually recursive names and their types (for termination checking), adding universes, see the note in TcTerm.fs:build_let_rec_env about usage of this field *)
  top_level      :bool;                         (* is this a top-level term? if so, then discharge guards *)
  check_uvars    :bool;                         (* paranoid: re-typecheck unification variables *)
  use_eq         :bool;                         (* generate an equality constraint, rather than subtyping/subkinding *)
  is_iface       :bool;                         (* is the module we're currently checking an interface? *)
  admit          :bool;                         (* admit VCs in the current module *)
  lax            :bool;                         (* don't even generate VCs *)
  lax_universes  :bool;                         (* don't check universe constraints *)
  phase1         :bool;                         (* running in phase 1, phase 2 to come after *)
  failhard       :bool;                         (* don't try to carry on after a typechecking error *)
  nosynth        :bool;                         (* don't run synth tactics *)
  uvar_subtyping :bool;
  tc_term        :env -> term -> term*lcomp*guard_t; (* a callback to the type-checker; g |- e : M t wp *)
  type_of        :env -> term ->term*typ*guard_t; (* a callback to the type-checker; check_term g e = t ==> g |- e : Tot t *)
  universe_of    :env -> term -> universe;        (* a callback to the type-checker; g |- e : Tot (Type u) *)
  check_type_of  :bool -> env -> term -> typ -> guard_t;
  use_bv_sorts   :bool;                           (* use bv.sort for a bound-variable's type rather than consulting gamma *)
  qtbl_name_and_index:BU.smap<int> * option<(lident*int)>;    (* the top-level term we're currently processing and the nth query for it, in addition we maintain a counter for query index per lid *)
  normalized_eff_names:BU.smap<lident>;           (* cache for normalized effect name, used to be captured in the function norm_eff_name, which made it harder to roll back etc. *)
  fv_delta_depths:BU.smap<delta_depth>;           (* cache for fv delta depths, its preferable to use Env.delta_depth_of_fv, soon fv.delta_depth should be removed *)
  proof_ns       :proof_namespace;                (* the current names that will be encoded to SMT (a.k.a. hint db) *)
  synth_hook          :env -> typ -> term -> term;     (* hook for synthesizing terms via tactics, third arg is tactic term *)
  splice         :env -> term -> list<sigelt>;    (* hook for synthesizing terms via tactics, third arg is tactic term *)
  mpreprocess    :env -> term -> term -> term;    (* hook for preprocessing typechecked terms via metaprograms *)
  postprocess    :env -> term -> typ -> term -> term; (* hook for postprocessing typechecked terms via metaprograms *)
  is_native_tactic: lid -> bool;                  (* callback into the native tactics engine *)
  identifier_info: ref<FStar.TypeChecker.Common.id_info_table>; (* information on identifiers *)
  tc_hooks       : tcenv_hooks;                   (* hooks that the interactive more relies onto for symbol tracking *)
  dsenv          : FStar.Syntax.DsEnv.env;        (* The desugaring environment from the front-end *)
  nbe            : list<step> -> env -> term -> term;  (* Callback to the NBE function *)
  strict_args_tab:BU.smap<(option<(list<int>)>)>;  (* a dictionary of fv names to strict arguments *)
  erasable_types_tab:BU.smap<bool>;              (* a dictionary of type names to erasable types *)
}

and solver_depth_t = int * int * int
and solver_t = {
    init         :env -> unit;
    push         :string -> unit;
    pop          :string -> unit;
    snapshot     :string -> (solver_depth_t * unit);
    rollback     :string -> option<solver_depth_t> -> unit;
    encode_sig   :env -> sigelt -> unit;
    preprocess   :env -> goal -> list<(env * goal * FStar.Options.optionstate)>;
    solve        :option<(unit -> string)> -> env -> goal -> unit; //call to the smt solver
    finish       :unit -> unit;
    refresh      :unit -> unit;
}
and tcenv_hooks =
  { tc_push_in_gamma_hook : (env -> BU.either<binding, sig_binding> -> unit) }

type implicit = TcComm.implicit
type implicits = TcComm.implicits
type guard_t = TcComm.guard_t

val tc_hooks : env -> tcenv_hooks
val set_tc_hooks: env -> tcenv_hooks -> env
val preprocess : env -> term -> term -> term
val postprocess : env -> term -> typ -> term -> term

type env_t = env
val initial_env : FStar.Parser.Dep.deps ->
                  (env -> term -> term*lcomp*guard_t) ->
                  (env -> term -> term*typ*guard_t) ->
                  (env -> term -> universe) ->
                  (bool -> env -> term -> typ -> guard_t) ->
                  solver_t -> lident ->
                  (list<step> -> env -> term -> term) -> env

(* Some utilities *)
val should_verify   : env -> bool
val incr_query_index: env -> env
val string_of_delta_level : delta_level -> string
val rename_gamma : subst_t -> gamma -> gamma
val rename_env : subst_t -> env -> env
val set_dep_graph: env -> FStar.Parser.Dep.deps -> env
val dep_graph: env -> FStar.Parser.Dep.deps

val dsenv : env -> FStar.Syntax.DsEnv.env

(* Marking and resetting the environment *)
val push : env -> string -> env
val pop : env -> string -> env

type tcenv_depth_t = int * int * solver_depth_t * int
val snapshot : env -> string -> (tcenv_depth_t * env)
val rollback : solver_t -> string -> option<tcenv_depth_t> -> env

(* Checking the per-module debug level and position info *)
val debug          : env -> Options.debug_level_t -> bool
val current_module : env -> lident
val set_range      : env -> Range.range -> env
val get_range      : env -> Range.range
val insert_bv_info : env -> bv -> typ -> unit
val insert_fv_info : env -> fv -> typ -> unit
val toggle_id_info : env -> bool -> unit
val promote_id_info : env -> (typ -> typ) -> unit

type qninfo = option<(BU.either<(universes * typ),(sigelt * option<universes>)> * Range.range)>

(* Querying identifiers *)
val lid_exists             : env -> lident -> bool
val try_lookup_bv          : env -> bv -> option<(typ * Range.range)>
val lookup_bv              : env -> bv -> typ * Range.range
val lookup_qname           : env -> lident -> qninfo
val lookup_sigelt          : env -> lident -> option<sigelt>
val try_lookup_lid         : env -> lident -> option<((universes * typ) * Range.range)>
val try_lookup_and_inst_lid: env -> universes -> lident -> option<(typ * Range.range)>
val lookup_lid             : env -> lident -> (universes * typ) * Range.range
val lookup_univ            : env -> univ_name -> bool
val try_lookup_val_decl    : env -> lident -> option<(tscheme * list<qualifier>)>
val lookup_val_decl        : env -> lident -> (universes * typ)
val lookup_datacon         : env -> lident -> universes * typ
(* the boolean tells if the lident was actually a inductive *)
val datacons_of_typ        : env -> lident -> (bool * list<lident>)
val typ_of_datacon         : env -> lident -> lident
val lookup_definition_qninfo : list<delta_level> -> lident -> qninfo -> option<(univ_names * term)>
val lookup_definition      : list<delta_level> -> env -> lident -> option<(univ_names * term)>
val lookup_nonrec_definition: list<delta_level> -> env -> lident -> option<(univ_names * term)>
val quals_of_qninfo        : qninfo -> option<list<qualifier>>
val attrs_of_qninfo        : qninfo -> option<list<attribute>>
val lookup_attrs_of_lid    : env -> lid -> option<list<attribute>>
val fv_with_lid_has_attr   : env -> fv_lid:lid -> attr_lid:lid -> bool
val fv_has_attr            : env -> fv -> attr_lid:lid -> bool
val fv_has_strict_args     : env -> fv -> option<(list<int>)>
val non_informative        : env -> typ -> bool
val try_lookup_effect_lid  : env -> lident -> option<term>
val lookup_effect_lid      : env -> lident -> term
val lookup_effect_abbrev   : env -> universes -> lident -> option<(binders * comp)>
val norm_eff_name          : (env -> lident -> lident)
val num_effect_indices     : env -> lident -> Range.range -> int
val lookup_effect_quals    : env -> lident -> list<qualifier>
val lookup_projector       : env -> lident -> int -> lident
val lookup_attr            : env -> string -> list<sigelt>
val is_projector           : env -> lident -> bool
val is_datacon             : env -> lident -> bool
val is_record              : env -> lident -> bool
val qninfo_is_action       : qninfo -> bool
val is_action              : env -> lident -> bool
val is_interpreted         : (env -> term -> bool)
val is_irreducible         : env -> lident -> bool
val is_type_constructor    : env -> lident -> bool
val num_inductive_ty_params: env -> lident -> option<int>
val delta_depth_of_qninfo  : fv -> qninfo -> option<delta_depth>
val delta_depth_of_fv      : env -> fv -> delta_depth

(* Universe instantiation *)

(* Construct a new universe unification variable *)
val new_u_univ             : unit -> universe
val inst_tscheme_with      : tscheme -> universes -> universes * term
(* Instantiate the universe variables in a type scheme with new unification variables *)
val inst_tscheme           : tscheme -> universes * term
val inst_effect_fun_with   : universes -> env -> eff_decl -> tscheme -> term
val mk_univ_subst          : list<univ_name> -> universes -> list<subst_elt>

(* Introducing identifiers and updating the environment *)

(*
 * push_sigelt only adds the sigelt to various caches maintained by env
 * For semantic changes, such as adding an effect or adding an edge to the effect lattice,
 *   Tc calls separate functions
 *)
val push_sigelt           : env -> sigelt -> env
val push_new_effect       : env -> (eff_decl * list<qualifier>) -> env

//client constructs the mlift and gives it to us
val update_effect_lattice : env -> src:lident -> tgt:lident -> mlift -> env

val push_bv               : env -> bv -> env
val push_bvs              : env -> list<bv> -> env
val pop_bv                : env -> option<(bv * env)>
val push_let_binding      : env -> lbname -> tscheme -> env
val push_binders          : env -> binders -> env
val push_univ_vars        : env -> univ_names -> env
val open_universes_in     : env -> univ_names -> list<term> -> env * univ_names * list<term>
val set_expected_typ      : env -> typ -> env
val expected_typ          : env -> option<typ>
val clear_expected_typ    : env -> env*option<typ>
val set_current_module    : env -> lident -> env
val finish_module         : (env -> modul -> env)

(* Collective state of the environment *)
val bound_vars   : env -> list<bv>
val all_binders  : env -> binders
val modules      : env -> list<modul>
val uvars_in_env : env -> uvars
val univ_vars    : env -> FStar.Util.set<universe_uvar>
val univnames    : env -> FStar.Util.set<univ_name>
val lidents      : env -> list<lident>

(* operations on monads *)
val identity_mlift         : mlift
val join                   : env -> lident -> lident -> lident * mlift * mlift
val monad_leq              : env -> lident -> lident -> option<edge>
val effect_decl_opt        : env -> lident -> option<(eff_decl * list<qualifier>)>
val get_effect_decl        : env -> lident -> eff_decl
val is_layered_effect      : env -> lident -> bool
val wp_signature           : env -> lident -> (bv * term)
val comp_to_comp_typ       : env -> comp -> comp_typ
val unfold_effect_abbrev   : env -> comp -> comp_typ
val effect_repr            : env -> comp -> universe -> option<term>
val reify_comp             : env -> comp -> universe -> term

(* [is_reifiable_* env x] returns true if the effect name/computational effect (of *)
(* a body or codomain of an arrow) [x] is reifiable *)
val is_reifiable_effect      : env -> lident -> bool
val is_reifiable_rc          : env -> residual_comp -> bool
val is_reifiable_comp        : env -> comp -> bool
val is_reifiable_function    : env -> term -> bool

(* [is_user_reifiable_* env x] is more restrictive, and only allows *)
(* reifying effects marked with the `reifiable` keyword. (For instance, TAC *)
(* is reifiable but not user-reifiable.) *)
val is_user_reifiable_effect : env -> lident -> bool
val is_user_reflectable_effect : env -> lident -> bool

(* Is this effect marked `total`? *)
val is_total_effect : env -> lident -> bool

(* A coercion *)
val binders_of_bindings : list<binding> -> binders

(* Toggling of encoding of namespaces *)
val should_enc_path : env -> list<string> -> bool
val should_enc_lid  : env -> lident -> bool
val add_proof_ns    : env -> name_prefix -> env
val rem_proof_ns    : env -> name_prefix -> env
val get_proof_ns    : env -> proof_namespace
val set_proof_ns    : proof_namespace -> env -> env
val string_of_proof_ns : env -> string

(* Check that all free variables of the term are defined in the environment *)
val unbound_vars    : env -> term -> BU.set<bv>
val closed          : env -> term -> bool
val closed'         : term -> bool

(* Operations on guard_t *)
val close_guard_univs         : universes -> binders -> guard_t -> guard_t
val close_guard               : env -> binders -> guard_t -> guard_t  //this closes the guard formula with bs
val apply_guard               : guard_t -> term -> guard_t
val map_guard                 : guard_t -> (term -> term) -> guard_t
val always_map_guard          : guard_t -> (term -> term) -> guard_t
val trivial_guard             : guard_t
val is_trivial                : guard_t -> bool
val is_trivial_guard_formula  : guard_t -> bool
val conj_guard                : guard_t -> guard_t -> guard_t
val conj_guards               : list<guard_t> -> guard_t
val abstract_guard            : binder -> guard_t -> guard_t
val abstract_guard_n          : list<binder> -> guard_t -> guard_t
val imp_guard                 : guard_t -> guard_t -> guard_t
val guard_of_guard_formula    : guard_formula -> guard_t
val guard_form                : guard_t -> guard_formula
val check_trivial             : term -> guard_formula

(* Other utils *)
val def_check_closed_in       : Range.range -> msg:string -> scope:list<bv> -> term -> unit
val def_check_closed_in_env   : Range.range -> msg:string -> env -> term -> unit
val def_check_guard_wf        : Range.range -> msg:string -> env -> guard_t -> unit
val close_forall              : env -> binders -> term -> term

val new_implicit_var_aux : string -> Range.range -> env -> typ -> should_check_uvar -> option<(FStar.Dyn.dyn * term)> -> (term * list<(ctx_uvar * Range.range)> * guard_t)


val print_gamma : gamma -> string

(* layered effect utils *)

(*
 * This gadget is used when the typechecker applies the layered effect combinators
 *
 * Given (opened) bs = x_i:t_i, this function creates uvars ?u_i:t_i
 *
 * When creating a ?u_i, it performs the substitution substs@[x_j/?u_j] in t_i, forall j < i
 *   so that the t_i is well-typed in env
 *
 * It returns the list of the uvars, and combined guard (which essentially contains the uvars as implicits)
 *)

val uvars_for_binders : env -> bs:S.binders -> substs:S.subst_t -> reason:(S.binder -> string) -> r:Range.range -> (list<S.term> * guard_t)

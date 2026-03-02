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
module FStarC.TypeChecker.Env
open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.Ident
open FStarC.TypeChecker.Common
open FStarC.Class.Binders
open FStarC.Class.Deq
open FStarC.Class.Show
open FStarC.Class.Setlike

module S = FStarC.Syntax.Syntax
module TcComm = FStarC.TypeChecker.Common

type step =
  | Beta
  | Iota            //pattern matching
  | Zeta            //fixed points
  | ZetaFull        //fixed points, even under blocked matches
  | Exclude of step //the first three kinds are included by default, unless Excluded explicity
  | Weak            //Do not descend into binders
  | HNF             //Only produce a head normal form: Do not descend into function arguments or into binder types
  | Primops         //reduce primitive operators like +, -, *, /, etc.
  | Eager_unfolding
  | Inlining
  | DoNotUnfoldPureLets
  | UnfoldUntil of delta_depth
  | UnfoldOnly  of list FStarC.Ident.lid
  | UnfoldOnce  of list FStarC.Ident.lid
  | UnfoldFully of list FStarC.Ident.lid
  | UnfoldAttr  of list FStarC.Ident.lid
  | UnfoldQual  of list string
  | UnfoldNamespace of list string
  | DontUnfoldAttr of list lid
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
  | Unrefine
  | NormDebug       //force debugging
  | DefaultUnivsToZero // default al unresolved universe uvars to zero
  | Tactics
and steps = list step

instance val deq_step : deq step
instance val showable_step : showable step

type sig_binding = list lident & sigelt

type delta_level =
  | NoDelta
  | InliningDelta // ZP : Trying to resolve name clash
  | Eager_unfolding_only
  | Unfold of delta_depth

instance val deq_delta_level : deq delta_level
instance val showable_delta_level : showable delta_level

// A name prefix, such as ["FStar";"Math"]
type name_prefix = FStarC.Ident.path
// A choice of which name prefixes are enabled/disabled
// The leftmost match takes precedence. Empty list means everything is off.
// To turn off everything, one can prepend `([], false)` to this (since [] is a prefix of everything)
type proof_namespace = list (name_prefix & bool)

type cached_elt = (either (universes & typ) (sigelt & option universes)) & Range.t
type goal = term

type must_tot = bool

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

type lift_comp_t = env -> comp -> ML (comp & guard_t)

(*
 * AR: Env maintains polymonadic binds as functions of type polymonadic_bind_t
 *     read as: env -> c1 -> x -> c2 -> flags -> r -> (c * g)
 *)
and polymonadic_bind_t =
  env ->
  comp_typ ->
  option bv ->
  comp_typ ->
  list cflag ->
  Range.t ->
  ML (comp & guard_t)

and mlift = {
  mlift_wp:lift_comp_t;
  mlift_term:option (universe -> typ -> term -> ML term)
}

(*
 * Edge in the effect lattice
 *
 * May have been computed by composing other "edges"
 *)
and edge = {
  msource : lident;
  mtarget : lident;
  mlift   : mlift;
  mpath   : list lident;  //this is just for debugging pusposes
                           //e.g. it is used when printing the effects graph
                           //it has no other role
                           //the path is the list of nodes that the "edge" goes through
                           //not including msource and mtarget
}

(*
 * The effects graph
 *
 * Each of order, joins, polymonadic binds, subcomps, are lists,
 *   that may have multiple entries for same nodes,
 *   e.g. multiple edges between effects M and N
 *
 * We keep adding the latest ones to the head of the list,
 *   which is then picked for application
 *
 * I.e. we don't remove when overriding
 *)

and effects = {
  decls :list (eff_decl & list qualifier);
  order :list edge;                                       (* transitive closure of the order in the signature *)
  joins :list (lident & lident & lident & mlift & mlift); (* least upper bounds *)
  polymonadic_binds :list (lident & lident & lident & polymonadic_bind_t);  (* (m, n) | p *)
  polymonadic_subcomps :list (lident & lident & tscheme & S.indexed_effect_combinator_kind);  (* m <: n *)
}

and env = {
  solver         :solver_t;                     (* interface to the SMT solver *)
  range          :Range.t;                  (* the source location of the term being checked *)
  curmodule      :lident;                       (* Name of this module *)
  gamma          :list binding;                (* Local typing environment *)
  gamma_sig      :list sig_binding;            (* and signature elements *)
  gamma_cache    :SMap.t cached_elt;           (* Memo table for the global gamma_sig environment *)
  modules        :list modul;                  (* already fully type checked modules *)
  expected_typ   :option (typ & bool);         (* type expected by the context *)
                                                (* a true bool will check for type equality (else subtyping) *)
  sigtab         :SMap.t sigelt;              (* a dictionary of long-names to sigelts *)
  attrtab        :SMap.t (list sigelt);        (* a dictionary of attribute( name)s to sigelts, mostly in support of typeclasses *)
  instantiate_imp:bool;                         (* instantiate implicit arguments? default=true *)
  effects        :effects;                      (* monad lattice *)
  generalize     :bool;                         (* should we generalize let bindings? *)
  letrecs        :list (lbname & int & typ & univ_names);  (* mutually recursive names, with recursion arity and their types (for termination checking), adding universes, see the note in TcTerm.fs:build_let_rec_env about usage of this field *)
  top_level      :bool;                         (* is this a top-level term? if so, then discharge guards *)
  check_uvars    :bool;                         (* paranoid: re-typecheck unification variables *)
  use_eq_strict  :bool;                         (* this flag runs the typechecker in non-subtyping mode *)
                                                (* i.e. using type equality instead of subtyping *)
  is_iface       :bool;                         (* is the module we're currently checking an interface? *)
  admit          :bool;                         (* admit VCs in the current module *)
  phase1         :bool;                         (* running in phase 1, phase 2 to come after *)
  failhard       :bool;                         (* don't try to carry on after a typechecking error *)
  flychecking    :bool;                         (* currently flychecking in IDE, used to for example not run synth tactics *)
  uvar_subtyping :bool;
  intactics      :bool;                         (* we are currently running a tactic *)
  nocoerce       :bool;                         (* do not apply any coercions *)

  tc_term :env -> term -> ML (term & lcomp & guard_t); (* typechecker callback; G |- e : C <== g *)
  typeof_tot_or_gtot_term :env -> term -> must_tot -> ML (term & typ & guard_t); (* typechecker callback; G |- e : (G)Tot t <== g *)
  universe_of :env -> term -> ML universe; (* typechecker callback; G |- e : Tot (Type u) *)
  typeof_well_typed_tot_or_gtot_term :env -> term -> must_tot -> ML (typ & guard_t); (* typechecker callback, uses fast path, with a fallback on the slow path *)
  teq_nosmt_force: env -> term -> term -> ML bool;        (* callback to the unifier *)
  subtype_nosmt_force: env -> term -> term -> ML bool;    (* callback to the unifier *)
  qtbl_name_and_index: option (lident & typ & int) & SMap.t int;
     (* ^ the top-level term we're currently processing, its type, and the query counter for it,
       in addition we maintain a counter for query index per lid *)
  normalized_eff_names:SMap.t lident;           (* cache for normalized effect name, used to be captured in the function norm_eff_name, which made it harder to roll back etc. *)
  fv_delta_depths:SMap.t delta_depth;           (* cache for fv delta depths, its preferable to use Env.delta_depth_of_fv, soon fv.delta_depth should be removed *)
  proof_ns       :proof_namespace;                (* the current names that will be encoded to SMT (a.k.a. hint db) *)
  synth_hook          :env -> typ -> term -> Range.t -> ML term;     (* hook for synthesizing terms via tactics, third arg is tactic term *)
  try_solve_implicits_hook :env -> term -> implicits -> ML unit;     (* *)
  splice : splice_t;   (* hook for synthesizing top-level sigelts via tactics *)
  mpreprocess    :env -> term -> term -> ML term;    (* hook for preprocessing typechecked terms via metaprograms *)
  postprocess    :env -> term -> typ -> term -> ML term; (* hook for postprocessing typechecked terms via metaprograms *)
  identifier_info: ref FStarC.TypeChecker.Common.id_info_table; (* information on identifiers *)
  tc_hooks       : tcenv_hooks;                   (* hooks that the interactive more relies onto for symbol tracking *)
  dsenv          : FStarC.Syntax.DsEnv.env;        (* The desugaring environment from the front-end *)
  nbe            : list step -> env -> term -> ML term;  (* Callback to the NBE function *)
  strict_args_tab:SMap.t (option (list int));  (* a dictionary of fv names to strict arguments *)
  erasable_types_tab:SMap.t bool;              (* a dictionary of type names to erasable types *)
  enable_defer_to_tac: bool;                     (* Set by default; unset when running within a tactic itself, since we do not allow
                                                    a tactic to defer problems to another tactic via the attribute mechanism *)
  unif_allow_ref_guards:bool;                     (* Allow guards when unifying refinements, even when SMT is disabled *)
  erase_erasable_args: bool;                      (* This flag is set when running normalize_for_extraction, see Extraction.ML.Modul *)

  core_check: core_check_t;

  (* A set of names for which we are missing a declaration.
  Every val (Sig_declare_typ) is added here and removed
  only when a definition for it is checked. At the of checking a module,
  if anything remains here, we fail. *)
  missing_decl : RBSet.t lident;
}
and solver_depth_t = int & int & int
and solver_t = {
    init            :env -> ML unit;
    // push            :string -> unit;
    // pop             :string -> unit;
    snapshot        :string -> ML (solver_depth_t & unit);
    rollback        :string -> option solver_depth_t -> ML unit;
    encode_sig      :env -> sigelt -> ML unit;
    preprocess      :env -> goal -> ML (bool & list (env & goal & FStarC.Options.optionstate));
    spinoff_strictly_positive_goals: option (env -> goal -> ML (list (env & goal)));
    handle_smt_goal :env -> goal -> ML (list (env & goal));
    solve           :option (unit -> ML string) -> env -> goal -> ML unit; //call to the smt solver
    solve_sync      :option (unit -> ML string) -> env -> goal -> ML bool; //call to the smt solver
    finish          :unit -> ML unit;
    refresh         :option proof_namespace -> ML unit;
}
and tcenv_hooks =
  { tc_push_in_gamma_hook : (env -> either binding sig_binding -> ML unit) }

and core_check_t =
  env -> term -> typ -> bool -> ML (either (option (typ & (unit -> ML unit))) (bool -> ML string))
and splice_t =
  env ->
  list S.qualifier ->       (* qualifiers in splice call *)
  list S.attribute ->       (* attributes in splice call *)
  is_typed:bool ->          (* is this a splice_t? *)
  list lident ->            (* list of names that MUST be defined *)
  term ->                   (* tactic term *)
  Range.t ->            (* entry range *)
  ML (list sigelt)

val rename_gamma : subst_t -> gamma -> ML gamma

val rename_env : subst_t -> env -> ML env

val tc_hooks : env -> tcenv_hooks

val set_tc_hooks: env -> tcenv_hooks -> env

val set_dep_graph: env -> FStarC.Parser.Dep.deps -> env

val dep_graph: env -> FStarC.Parser.Dep.deps

val with_restored_scope (e:env) (f:env -> ML ('a & env)) : ML ('a & env)
(* Keeping track of declarations and definitions. This operates
over the missing_decl field. *)

val preprocess : env -> term -> term -> ML (term)

val postprocess : env -> term -> typ -> term -> ML (term)

type env_t = env

val record_val_for (e:env) (l:lident) : ML env

val record_definition_for (e:env) (l:lident) : ML env

val missing_definition_list (e:env) : ML (list lident)

type implicit = TcComm.implicit
type implicits = TcComm.implicits
type guard_t = TcComm.guard_t
type tcenv_depth_t = int & int & solver_depth_t & int
type qninfo = option ((either (universes & typ) (sigelt & option universes)) & Range.t)

val should_verify   : env -> ML (bool)

val initial_env : FStarC.Parser.Dep.deps ->
                  (env -> term -> ML (term & lcomp & guard_t)) ->
                  (env -> term -> must_tot -> ML (term & typ & guard_t)) ->
                  (env -> term -> must_tot -> ML (option typ)) ->
                  (env -> term -> ML universe) ->
                  (env -> term -> term -> ML bool) ->
                  (env -> term -> term -> ML bool) ->
                  solver_t -> lident ->
                  (list step -> env -> term -> ML term) ->
                  core_check_t -> ML (env)

(* Some utilities *)

val dsenv : env -> FStarC.Syntax.DsEnv.env

(* Marking and resetting the environment *)

val snapshot : env -> string -> ML ((tcenv_depth_t & env))

val rollback : solver_t -> string -> option tcenv_depth_t -> ML (env)

(* Checking the per-module debug level and position info *)

val push : env -> string -> ML (env)

val pop : env -> string -> ML (env)

val incr_query_index: env -> ML (env)

val set_range      : env -> Range.t -> env

val get_range      : env -> Range.t

instance val hasRange_env : hasRange env

val toggle_id_info : env -> bool -> ML (unit)

val insert_bv_info : env -> bv -> typ -> ML (unit)

val insert_fv_info : env -> fv -> typ -> ML (unit)

val promote_id_info : env -> (typ -> ML (option typ)) -> ML (unit)

(* Querying identifiers *)

val modules      : env -> list modul

val current_module : env -> lident

val set_current_module    : env -> lident -> env

val new_u_univ             : unit -> ML universe

val mk_univ_subst          : list univ_name -> universes -> ML (list subst_elt)

(* Introducing identifiers and updating the environment *)

(*
 * push_sigelt only adds the sigelt to various caches maintained by env
 * For semantic changes, such as adding an effect or adding an edge to the effect lattice,
 *   Tc calls separate functions
 *)

val inst_tscheme_with      : tscheme -> universes -> ML (universes & term)
(* Instantiate the universe variables in a type scheme with new unification variables *)

val inst_tscheme           : tscheme -> ML (universes & term)

val inst_effect_fun_with   : universes -> env -> eff_decl -> tscheme -> ML (term)

val lookup_qname           : env -> lident -> ML (qninfo)

val lookup_sigelt          : env -> lident -> ML (option sigelt)

val lookup_attr            : env -> string -> ML (list sigelt)

val try_lookup_bv          : env -> bv -> ML (option (typ & Range.t))

val lid_exists             : env -> lident -> ML (bool)

val lookup_bv              : env -> bv -> ML (typ & Range.t)

val try_lookup_lid         : env -> lident -> ML (option ((universes & typ) & Range.t))

val try_lookup_and_inst_lid: env -> universes -> lident -> ML (option (typ & Range.t))

val lookup_lid             : env -> lident -> ML ((universes & typ) & Range.t)

val lookup_univ            : env -> univ_name -> ML (bool)

val try_lookup_val_decl    : env -> lident -> ML (option (tscheme & list qualifier))

val lookup_val_decl        : env -> lident -> ML ((universes & typ))

val lookup_datacon         : env -> lident -> ML (universes & typ)

val lookup_and_inst_datacon: env -> universes -> lident -> ML (typ)
(* the boolean tells if the lident was actually a inductive *)

val datacons_of_typ        : env -> lident -> ML ((bool & list lident))

val typ_of_datacon         : env -> lident -> ML (lident)

val num_datacon_non_injective_ty_params  : env -> lident -> ML (option int)

val visible_with           : list delta_level -> list qualifier -> ML (bool)

val lookup_definition_qninfo : list delta_level -> lident -> qninfo -> ML (option (univ_names & term))

val lookup_definition      : list delta_level -> env -> lident -> ML (option (univ_names & term))

val lookup_nonrec_definition: list delta_level -> env -> lident -> ML (option (univ_names & term))

val delta_depth_of_qninfo  : env -> fv -> qninfo -> ML (delta_depth)

val delta_depth_of_fv      : env -> fv -> ML (delta_depth)

(* Universe instantiation *)

(* Construct a new universe unification variable *)

val fv_delta_depth : env -> fv -> ML (delta_depth)

val delta_depth_of_term : env -> term -> ML (delta_depth)

val quals_of_qninfo        : qninfo -> option (list qualifier)

val attrs_of_qninfo        : qninfo -> option (list attribute)

val lookup_attrs_of_lid    : env -> lid -> ML (option (list attribute))

val fv_with_lid_has_attr   : env -> fv_lid:lid -> attr_lid:lid -> ML (bool)

val fv_has_attr            : env -> fv -> attr_lid:lid -> ML (bool)

val fv_has_erasable_attr   : env -> fv -> ML (bool)

val fv_has_strict_args     : env -> fv -> ML (option (list int))

val try_lookup_effect_lid  : env -> lident -> ML (option term)

val lookup_effect_lid      : env -> lident -> ML (term)

val lookup_effect_abbrev   : env -> universes -> lident -> ML (option (binders & comp))

val norm_eff_name          : (env -> lident -> ML (lident))

val is_erasable_effect     : env -> lident -> ML (bool)

(* [is_reifiable_* env x] returns true if the effect name/computational effect (of *)
(* a body or codomain of an arrow) [x] is reifiable *)

val non_informative        : env -> typ -> ML (bool)

val num_effect_indices     : env -> lident -> Range.t -> ML (int)

val lookup_effect_quals    : env -> lident -> ML (list qualifier)

val lookup_projector       : env -> lident -> int -> ML (lident)

val is_projector           : env -> lident -> ML (bool)

val is_datacon             : env -> lident -> ML (bool)

val is_record              : env -> lident -> ML (bool)

val qninfo_is_action       : qninfo -> ML (bool)

val is_action              : env -> lident -> ML (bool)

val is_interpreted         : (env -> term -> ML (bool))

val is_irreducible         : env -> lident -> ML (bool)

val is_type_constructor    : env -> lident -> ML (bool)

val num_inductive_ty_params: env -> lident -> ML (option int)

val num_inductive_uniform_ty_params: env -> lident -> ML (option int)

val effect_decl_opt        : env -> lident -> ML (option (eff_decl & list qualifier))

val get_effect_decl        : env -> lident -> ML (eff_decl)

val get_default_effect     : env -> lident -> ML (option lident)

val get_top_level_effect   : env -> lident -> ML (option lident)

val is_layered_effect      : env -> lident -> ML (bool)

val identity_mlift         : mlift

val join_opt               : env -> lident -> lident -> ML (option (lident & mlift & mlift))

val join                   : env -> lident -> lident -> ML (lident & mlift & mlift)

val monad_leq              : env -> lident -> lident -> ML (option edge)

val wp_signature           : env -> lident -> ML ((bv & term))

val binders_of_bindings : list binding -> ML (binders)

(* Toggling of encoding of namespaces *)

val all_binders  : env -> ML (binders)

val bound_vars   : env -> ML (list bv)

instance val hasBinders_env   : hasBinders env

instance val hasNames_lcomp   : hasNames lcomp

instance val pretty_lcomp     : FStarC.Class.PP.pretty lcomp

instance val hasNames_guard   : hasNames guard_t

instance val pretty_guard     : FStarC.Class.PP.pretty guard_t

val comp_to_comp_typ       : env -> comp -> ML (comp_typ)

val comp_set_flags         : env -> comp -> list S.cflag -> ML (comp)

val unfold_effect_abbrev   : env -> comp -> ML (comp_typ)

val effect_repr            : env -> comp -> universe -> ML (option term)

val is_user_reifiable_effect : env -> lident -> ML (bool)

val is_user_reflectable_effect : env -> lident -> ML (bool)

(* Is this effect marked `total`? *)

val is_total_effect : env -> lident -> ML (bool)

(* A coercion *)

val is_reifiable_effect      : env -> lident -> ML (bool)

val is_reifiable_rc          : env -> residual_comp -> ML (bool)

val is_reifiable_comp        : env -> comp -> ML (bool)

val is_reifiable_function    : env -> term -> ML (bool)

(* [is_user_reifiable_* env x] is more restrictive, and only allows *)
(* reifying effects marked with the `reifiable` keyword. (For instance, TAC *)
(* is reifiable but not user-reifiable.) *)

val reify_comp             : env -> comp -> universe -> ML (term)

val push_sigelt           : env -> sigelt -> ML env

val push_sigelt_force     : env -> sigelt -> ML env (* does not check for repeats *)

val push_new_effect       : env -> (eff_decl & list qualifier) -> env

//client constructs the mlift and gives it to us

val exists_polymonadic_bind: env -> lident -> lident -> ML (option (lident & polymonadic_bind_t))

val exists_polymonadic_subcomp: env -> lident -> lident -> ML (option (tscheme & S.indexed_effect_combinator_kind))

//print the effects graph in dot format

val print_effects_graph: env -> ML (string)

val update_effect_lattice  : env -> src:lident -> tgt:lident -> mlift -> ML (env)

val add_polymonadic_bind   : env -> m:lident -> n:lident -> p:lident -> polymonadic_bind_t -> env

val add_polymonadic_subcomp: env -> m:lident -> n:lident -> (tscheme & S.indexed_effect_combinator_kind) -> env

val push_bv               : env -> bv -> env

val push_bvs              : env -> list bv -> ML (env)

val pop_bv                : env -> option (bv & env)

val push_binders          : env -> binders -> ML (env)

val push_let_binding      : env -> lbname -> tscheme -> env

val push_univ_vars        : env -> univ_names -> ML (env)

val open_universes_in     : env -> univ_names -> list term -> ML (env & univ_names & list term)

val set_expected_typ      : env -> typ -> env

val set_expected_typ_maybe_eq
                          : env -> typ -> bool -> env  //boolean true will check for type equality

//the returns boolean true means check for type equality

val expected_typ          : env -> option (typ & bool)

val clear_expected_typ    : env -> env&option (typ & bool)

val finish_module         : (env -> modul -> env)

(* Collective state of the environment *)

val uvars_in_env : env -> ML (uvars)

val univ_vars    : env -> ML (FlatSet.t universe_uvar)

val univnames    : env -> ML (FlatSet.t univ_name)

val lidents      : env -> ML (list lident)

(* operations on monads *)

val should_enc_lid  : proof_namespace -> lident -> ML (bool)

val add_proof_ns    : env -> name_prefix -> env

val rem_proof_ns    : env -> name_prefix -> env

val get_proof_ns    : env -> proof_namespace

val set_proof_ns    : proof_namespace -> env -> env

val unbound_vars    : env -> term -> ML (FlatSet.t bv)

val closed          : env -> term -> ML (bool)

val closed'         : term -> ML bool

(* Operations on guard_t *)

val string_of_proof_ns : env -> ML (string)

(* Check that all free variables of the term are defined in the environment *)

val guard_of_guard_formula    : guard_formula -> guard_t

val guard_form                : guard_t -> guard_formula

val is_trivial                : guard_t -> ML (bool)

val is_trivial_guard_formula  : guard_t -> bool

val trivial_guard             : guard_t

val abstract_guard_n          : list binder -> guard_t -> ML (guard_t)

val abstract_guard            : binder -> guard_t -> ML (guard_t)

val too_early_in_prims : env -> ML (bool)

val apply_guard               : guard_t -> term -> ML (guard_t)

val map_guard                 : guard_t -> (term -> ML term) -> ML guard_t

val always_map_guard          : guard_t -> (term -> ML term) -> ML guard_t

val check_trivial             : term -> ML (guard_formula)

(* Other utils *)

val conj_guard                : guard_t -> guard_t -> ML (guard_t)

val conj_guards               : list guard_t -> ML (guard_t)

val imp_guard                 : guard_t -> guard_t -> ML (guard_t)

val close_guard_univs         : universes -> binders -> guard_t -> ML (guard_t)

val close_forall              : env -> binders -> term -> ML (term)

val close_guard               : env -> binders -> guard_t -> ML (guard_t) //this closes the guard formula with bs

val new_tac_implicit_var
  (reason: string)
  (r: Range.t)
  (env:env)
  (uvar_typ:typ)
  (should_check:should_check_uvar)
  (uvar_typedness_deps:list ctx_uvar)
  (meta:option ctx_uvar_meta_t)
  (unrefine:bool)
: ML (term & (ctx_uvar & Range.t) & guard_t)

val new_implicit_var_aux
  (reason: string)
  (r: Range.t)
  (env:env)
  (uvar_typ:typ)
  (should_check:should_check_uvar)
  (meta:option ctx_uvar_meta_t)
  (unrefine:bool)
: ML (term & (ctx_uvar & Range.t) & guard_t)

val uvar_meta_for_binder (b:binder) : ML (option ctx_uvar_meta_t & (*should_unrefine:*)bool)

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

val uvars_for_binders :
  env ->
  bs:S.binders ->
  substs:S.subst_t ->
  reason:(S.binder -> ML string) ->
  r:Range.t -> ML ((list S.term & guard_t))

val pure_precondition_for_trivial_post : env -> universe -> typ -> typ -> Range.t -> ML (typ)

(* Fetch the arity from the letrecs field. None if not there (happens
for either not a recursive let, or one that does not need the totality
check. *)

val get_letrec_arity : env -> lbname -> ML (option int)

(* Construct a Tm_fvar with the delta_depth metadata populated
   -- Note, the delta_qual is not populated, so don't use this with
      Data constructors, projectors, record identifiers etc.

   -- Also, don't use this with lidents that refer to Prims, that
      still requires special handling
*)

val fvar_of_nonqual_lid : env -> lident -> ML (term)

val split_smt_query : env -> term -> ML (option (list (env & term)))

(* Binding instances, mostly for defensive checks *)

instance val hashable_env : Class.Hashable.hashable env


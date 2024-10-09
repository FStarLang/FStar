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
open FStar.Pervasives
open FStarC.Compiler.Effect
open FStar open FStarC
open FStarC.Compiler
open FStarC.Syntax.Syntax
open FStarC.Ident
open FStarC.TypeChecker.Common
open FStarC.Class.Binders
open FStarC.Class.Deq
open FStarC.Class.Show
open FStarC.Class.Setlike

module BU = FStarC.Compiler.Util
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

type cached_elt = (either (universes & typ) (sigelt & option universes)) & Range.range
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

type lift_comp_t = env -> comp -> comp & guard_t

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
  Range.range ->
  comp & guard_t

and mlift = {
  mlift_wp:lift_comp_t;
  mlift_term:option (universe -> typ -> term -> term)
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
  range          :Range.range;                  (* the source location of the term being checked *)
  curmodule      :lident;                       (* Name of this module *)
  gamma          :list binding;                (* Local typing environment *)
  gamma_sig      :list sig_binding;            (* and signature elements *)
  gamma_cache    :FStarC.Compiler.Util.smap cached_elt;  (* Memo table for the global gamma_sig environment *)
  modules        :list modul;                  (* already fully type checked modules *)
  expected_typ   :option (typ & bool);         (* type expected by the context *)
                                                (* a true bool will check for type equality (else subtyping) *)
  sigtab         :BU.smap sigelt;              (* a dictionary of long-names to sigelts *)
  attrtab        :BU.smap (list sigelt);        (* a dictionary of attribute( name)s to sigelts, mostly in support of typeclasses *)
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
  lax_universes  :bool;                         (* don't check universe constraints *)
  phase1         :bool;                         (* running in phase 1, phase 2 to come after *)
  failhard       :bool;                         (* don't try to carry on after a typechecking error *)
  flychecking    :bool;                         (* currently flychecking in IDE, used to for example not run synth tactics *)
  uvar_subtyping :bool;
  intactics      :bool;                         (* we are currently running a tactic *)
  nocoerce       :bool;                         (* do not apply any coercions *)

  tc_term :env -> term -> term & lcomp & guard_t; (* typechecker callback; G |- e : C <== g *)
  typeof_tot_or_gtot_term :env -> term -> must_tot -> term & typ & guard_t; (* typechecker callback; G |- e : (G)Tot t <== g *)
  universe_of :env -> term -> universe; (* typechecker callback; G |- e : Tot (Type u) *)
  typeof_well_typed_tot_or_gtot_term :env -> term -> must_tot -> typ & guard_t; (* typechecker callback, uses fast path, with a fallback on the slow path *)
  teq_nosmt_force: env -> term -> term -> bool;        (* callback to the unifier *)
  subtype_nosmt_force: env -> term -> term -> bool;    (* callback to the unifier *)
  qtbl_name_and_index: option (lident & typ & int) & BU.smap int;
     (* ^ the top-level term we're currently processing, its type, and the query counter for it,
       in addition we maintain a counter for query index per lid *)
  normalized_eff_names:BU.smap lident;           (* cache for normalized effect name, used to be captured in the function norm_eff_name, which made it harder to roll back etc. *)
  fv_delta_depths:BU.smap delta_depth;           (* cache for fv delta depths, its preferable to use Env.delta_depth_of_fv, soon fv.delta_depth should be removed *)
  proof_ns       :proof_namespace;                (* the current names that will be encoded to SMT (a.k.a. hint db) *)
  synth_hook          :env -> typ -> term -> term;     (* hook for synthesizing terms via tactics, third arg is tactic term *)
  try_solve_implicits_hook :env -> term -> implicits -> unit;     (* *)
  splice : env -> is_typed:bool -> list lident -> term -> Range.range -> list sigelt; (* hook for synthesizing top-level sigelts via tactics *)
                                                                                 (* second arg is true for typed splice *)
                                                                                 (* third arg is tactic term *)
  mpreprocess    :env -> term -> term -> term;    (* hook for preprocessing typechecked terms via metaprograms *)
  postprocess    :env -> term -> typ -> term -> term; (* hook for postprocessing typechecked terms via metaprograms *)
  identifier_info: ref FStarC.TypeChecker.Common.id_info_table; (* information on identifiers *)
  tc_hooks       : tcenv_hooks;                   (* hooks that the interactive more relies onto for symbol tracking *)
  dsenv          : FStarC.Syntax.DsEnv.env;        (* The desugaring environment from the front-end *)
  nbe            : list step -> env -> term -> term;  (* Callback to the NBE function *)
  strict_args_tab:BU.smap (option (list int));  (* a dictionary of fv names to strict arguments *)
  erasable_types_tab:BU.smap bool;              (* a dictionary of type names to erasable types *)
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
    init            :env -> unit;
    // push            :string -> unit;
    // pop             :string -> unit;
    snapshot        :string -> (solver_depth_t & unit);
    rollback        :string -> option solver_depth_t -> unit;
    encode_sig      :env -> sigelt -> unit;
    preprocess      :env -> goal -> bool & list (env & goal & FStarC.Options.optionstate);
    spinoff_strictly_positive_goals: option (env -> goal -> list (env & goal));
    handle_smt_goal :env -> goal -> list (env & goal);
    solve           :option (unit -> string) -> env -> goal -> unit; //call to the smt solver
    solve_sync      :option (unit -> string) -> env -> goal -> bool; //call to the smt solver
    finish          :unit -> unit;
    refresh         :option proof_namespace -> unit;
}
and tcenv_hooks =
  { tc_push_in_gamma_hook : (env -> either binding sig_binding -> unit) }

and core_check_t =
  env -> term -> typ -> bool -> either (option typ) (bool -> string)

(* Keeping track of declarations and definitions. This operates
over the missing_decl field. *)
val record_val_for (e:env) (l:lident) : env
val record_definition_for (e:env) (l:lident) : env
val missing_definition_list (e:env) : list lident

type implicit = TcComm.implicit
type implicits = TcComm.implicits
type guard_t = TcComm.guard_t
type tcenv_depth_t = int & int & solver_depth_t & int
type qninfo = option ((either (universes & typ) (sigelt & option universes)) & Range.range)

val tc_hooks : env -> tcenv_hooks
val set_tc_hooks: env -> tcenv_hooks -> env
val preprocess : env -> term -> term -> term
val postprocess : env -> term -> typ -> term -> term

type env_t = env

val initial_env : FStarC.Parser.Dep.deps ->
                  (env -> term -> term & lcomp & guard_t) ->
                  (env -> term -> must_tot -> term & typ & guard_t) ->
                  (env -> term -> must_tot -> option typ) ->
                  (env -> term -> universe) ->
                  (env -> term -> term -> bool) ->
                  (env -> term -> term -> bool) ->
                  solver_t -> lident ->
                  (list step -> env -> term -> term) ->
                  core_check_t -> env

(* Some utilities *)
val should_verify   : env -> bool
val incr_query_index: env -> env
val rename_gamma : subst_t -> gamma -> gamma
val rename_env : subst_t -> env -> env
val set_dep_graph: env -> FStarC.Parser.Dep.deps -> env
val dep_graph: env -> FStarC.Parser.Dep.deps

val dsenv : env -> FStarC.Syntax.DsEnv.env

(* Marking and resetting the environment *)
val push : env -> string -> env
val pop : env -> string -> env

val snapshot : env -> string -> (tcenv_depth_t & env)
val rollback : solver_t -> string -> option tcenv_depth_t -> env

(* Checking the per-module debug level and position info *)
val current_module : env -> lident
val set_range      : env -> Range.range -> env
val get_range      : env -> Range.range

instance val hasRange_env : hasRange env

val insert_bv_info : env -> bv -> typ -> unit
val insert_fv_info : env -> fv -> typ -> unit
val toggle_id_info : env -> bool -> unit
val promote_id_info : env -> (typ -> option typ) -> unit

(* Querying identifiers *)
val lid_exists             : env -> lident -> bool
val try_lookup_bv          : env -> bv -> option (typ & Range.range)
val lookup_bv              : env -> bv -> typ & Range.range
val lookup_qname           : env -> lident -> qninfo
val lookup_sigelt          : env -> lident -> option sigelt
val try_lookup_lid         : env -> lident -> option ((universes & typ) & Range.range)
val try_lookup_and_inst_lid: env -> universes -> lident -> option (typ & Range.range)
val lookup_lid             : env -> lident -> (universes & typ) & Range.range
val lookup_univ            : env -> univ_name -> bool
val try_lookup_val_decl    : env -> lident -> option (tscheme & list qualifier)
val lookup_val_decl        : env -> lident -> (universes & typ)
val lookup_datacon         : env -> lident -> universes & typ
val lookup_and_inst_datacon: env -> universes -> lident -> typ
(* the boolean tells if the lident was actually a inductive *)
val datacons_of_typ        : env -> lident -> (bool & list lident)
val typ_of_datacon         : env -> lident -> lident
val visible_with           : list delta_level -> list qualifier -> bool
val lookup_definition_qninfo : list delta_level -> lident -> qninfo -> option (univ_names & term)
val lookup_definition      : list delta_level -> env -> lident -> option (univ_names & term)
val lookup_nonrec_definition: list delta_level -> env -> lident -> option (univ_names & term)
val quals_of_qninfo        : qninfo -> option (list qualifier)
val attrs_of_qninfo        : qninfo -> option (list attribute)
val lookup_attrs_of_lid    : env -> lid -> option (list attribute)
val fv_with_lid_has_attr   : env -> fv_lid:lid -> attr_lid:lid -> bool
val fv_has_attr            : env -> fv -> attr_lid:lid -> bool
val fv_has_strict_args     : env -> fv -> option (list int)
val fv_has_erasable_attr   : env -> fv -> bool

(* `non_informative env t` is `Some i` if the type `t: Type` is noninformative,
   and any `x: t ...` can be erased to `i`. *)
val non_informative        : env -> typ -> option term

val try_lookup_effect_lid  : env -> lident -> option term
val lookup_effect_lid      : env -> lident -> term
val lookup_effect_abbrev   : env -> universes -> lident -> option (binders & comp)
val norm_eff_name          : (env -> lident -> lident)
val num_effect_indices     : env -> lident -> Range.range -> int
val lookup_effect_quals    : env -> lident -> list qualifier
val lookup_projector       : env -> lident -> int -> lident
val lookup_attr            : env -> string -> list sigelt
val is_projector           : env -> lident -> bool
val is_datacon             : env -> lident -> bool
val is_record              : env -> lident -> bool
val qninfo_is_action       : qninfo -> bool
val is_action              : env -> lident -> bool
val is_interpreted         : (env -> term -> bool)
val is_irreducible         : env -> lident -> bool
val is_type_constructor    : env -> lident -> bool
val num_inductive_ty_params: env -> lident -> option int
val num_inductive_uniform_ty_params: env -> lident -> option int
val num_datacon_non_injective_ty_params  : env -> lident -> option int
val delta_depth_of_qninfo  : env -> fv -> qninfo -> delta_depth
val delta_depth_of_fv      : env -> fv -> delta_depth

(* Universe instantiation *)

(* Construct a new universe unification variable *)
val new_u_univ             : unit -> universe
val inst_tscheme_with      : tscheme -> universes -> universes & term
(* Instantiate the universe variables in a type scheme with new unification variables *)
val inst_tscheme           : tscheme -> universes & term
val inst_effect_fun_with   : universes -> env -> eff_decl -> tscheme -> term
val mk_univ_subst          : list univ_name -> universes -> list subst_elt

(* Introducing identifiers and updating the environment *)

(*
 * push_sigelt only adds the sigelt to various caches maintained by env
 * For semantic changes, such as adding an effect or adding an edge to the effect lattice,
 *   Tc calls separate functions
 *)
val push_sigelt           : env -> sigelt -> env
val push_sigelt_force     : env -> sigelt -> env (* does not check for repeats *)
val push_new_effect       : env -> (eff_decl & list qualifier) -> env

//client constructs the mlift and gives it to us

val exists_polymonadic_bind: env -> lident -> lident -> option (lident & polymonadic_bind_t)
val exists_polymonadic_subcomp: env -> lident -> lident -> option (tscheme & S.indexed_effect_combinator_kind)

//print the effects graph in dot format
val print_effects_graph: env -> string

val update_effect_lattice  : env -> src:lident -> tgt:lident -> mlift -> env

val join_opt               : env -> lident -> lident -> option (lident & mlift & mlift)
val add_polymonadic_bind   : env -> m:lident -> n:lident -> p:lident -> polymonadic_bind_t -> env
val add_polymonadic_subcomp: env -> m:lident -> n:lident -> (tscheme & S.indexed_effect_combinator_kind) -> env

val push_bv               : env -> bv -> env
val push_bvs              : env -> list bv -> env
val pop_bv                : env -> option (bv & env)
val push_let_binding      : env -> lbname -> tscheme -> env
val push_binders          : env -> binders -> env
val push_univ_vars        : env -> univ_names -> env
val open_universes_in     : env -> univ_names -> list term -> env & univ_names & list term
val set_expected_typ      : env -> typ -> env
val set_expected_typ_maybe_eq
                          : env -> typ -> bool -> env  //boolean true will check for type equality

//the returns boolean true means check for type equality
val expected_typ          : env -> option (typ & bool)
val clear_expected_typ    : env -> env&option (typ & bool)

val set_current_module    : env -> lident -> env
val finish_module         : (env -> modul -> env)

(* Collective state of the environment *)
val bound_vars   : env -> list bv
val all_binders  : env -> binders
val modules      : env -> list modul
val uvars_in_env : env -> uvars
val univ_vars    : env -> FlatSet.t universe_uvar
val univnames    : env -> FlatSet.t univ_name
val lidents      : env -> list lident

(* operations on monads *)
val identity_mlift         : mlift
val join                   : env -> lident -> lident -> lident & mlift & mlift
val monad_leq              : env -> lident -> lident -> option edge
val effect_decl_opt        : env -> lident -> option (eff_decl & list qualifier)
val get_effect_decl        : env -> lident -> eff_decl
val get_default_effect     : env -> lident -> option lident
val get_top_level_effect   : env -> lident -> option lident
val is_layered_effect      : env -> lident -> bool
val wp_signature           : env -> lident -> (bv & term)
val comp_to_comp_typ       : env -> comp -> comp_typ
val comp_set_flags         : env -> comp -> list S.cflag -> comp
val unfold_effect_abbrev   : env -> comp -> comp_typ
val effect_repr            : env -> comp -> universe -> option term
val reify_comp             : env -> comp -> universe -> term

val is_erasable_effect     : env -> lident -> bool

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
val binders_of_bindings : list binding -> binders

(* Toggling of encoding of namespaces *)
val should_enc_lid  : proof_namespace -> lident -> bool
val add_proof_ns    : env -> name_prefix -> env
val rem_proof_ns    : env -> name_prefix -> env
val get_proof_ns    : env -> proof_namespace
val set_proof_ns    : proof_namespace -> env -> env
val string_of_proof_ns : env -> string

(* Check that all free variables of the term are defined in the environment *)
val unbound_vars    : env -> term -> FlatSet.t bv
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
val conj_guards               : list guard_t -> guard_t
val abstract_guard            : binder -> guard_t -> guard_t
val abstract_guard_n          : list binder -> guard_t -> guard_t
val imp_guard                 : guard_t -> guard_t -> guard_t
val guard_of_guard_formula    : guard_formula -> guard_t
val guard_form                : guard_t -> guard_formula
val check_trivial             : term -> guard_formula

(* Other utils *)
val too_early_in_prims : env -> bool

val close_forall              : env -> binders -> term -> term

val new_tac_implicit_var
  (reason: string)
  (r: Range.range)
  (env:env)
  (uvar_typ:typ)
  (should_check:should_check_uvar)
  (uvar_typedness_deps:list ctx_uvar)
  (meta:option ctx_uvar_meta_t)
  (unrefine:bool)
: term & (ctx_uvar & Range.range) & guard_t

val new_implicit_var_aux
  (reason: string)
  (r: Range.range)
  (env:env)
  (uvar_typ:typ)
  (should_check:should_check_uvar)
  (meta:option ctx_uvar_meta_t)
  (unrefine:bool)
: term & (ctx_uvar & Range.range) & guard_t


val uvar_meta_for_binder (b:binder) : option ctx_uvar_meta_t & (*should_unrefine:*)bool

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
  reason:(S.binder -> string) ->
  r:Range.range ->
  (list S.term & guard_t)

val pure_precondition_for_trivial_post : env -> universe -> typ -> typ -> Range.range -> typ

(* Fetch the arity from the letrecs field. None if not there (happens
for either not a recursive let, or one that does not need the totality
check. *)
val get_letrec_arity : env -> lbname -> option int

(* Construct a Tm_fvar with the delta_depth metadata populated
   -- Note, the delta_qual is not populated, so don't use this with
      Data constructors, projectors, record identifiers etc.

   -- Also, don't use this with lidents that refer to Prims, that
      still requires special handling
*)
val fvar_of_nonqual_lid : env -> lident -> term

val split_smt_query : env -> term -> option (list (env & term))

(* Binding instances, mostly for defensive checks *)

instance val hasBinders_env   : hasBinders env
instance val hasNames_lcomp   : hasNames lcomp
instance val pretty_lcomp     : FStarC.Class.PP.pretty lcomp
instance val hasNames_guard   : hasNames guard_t
instance val pretty_guard     : FStarC.Class.PP.pretty guard_t

val fv_delta_depth : env -> fv -> delta_depth
val delta_depth_of_term : env -> term -> delta_depth

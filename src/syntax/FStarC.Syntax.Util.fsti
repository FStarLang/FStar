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
module FStarC.Syntax.Util
open FStarC.Effect
open FStarC.List

open FStarC
open FStarC.Ident
open FStarC.Range.Type
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Const
open FStar.Dyn
open FStarC.Syntax.Subst

open FStarC.Class.Show
open FStarC.Class.Monad
open FStarC.Class.Setlike

(********************************************************************************)
(**************************Utilities for identifiers ****************************)
(********************************************************************************)

(* A hook into FStarC.Syntax.Print, only for debugging and error messages.
 * The reference is set in FStarC.Main *)
val tts_f : ref (option (term -> ML string))
val tts (t:term) : ML string
val ttd_f : ref (option (term -> ML Pprint.document))
val ttd (t:term) : ML Pprint.document

val mk_discriminator (lid:lident) : ML lident

(* is uppercase name like Cons *)
val is_name (lid:lident) : ML bool

val aqual_of_binder (b:binder) : aqual

val bqual_and_attrs_of_aqual (a:aqual) : bqual & list attribute

val arg_of_non_null_binder (b:binder) : ML arg

val args_of_non_null_binders (binders:binders) : ML args

val args_of_binders (binders:Syntax.binders) : ML (Syntax.binders & args)

val name_binders (bs:binders) : ML binders

val name_function_binders (t:term) : ML term

val subst_of_list (formals:binders) (actuals:args) : ML subst_t

val rename_binders (replace_xs:binders) (with_ys:binders) : ML subst_t

val unmeta : term -> ML term
val unmeta_safe : term -> ML term
val unmeta_lift : term -> ML term

(********************************************************************************)
(*************************** Utilities for universes ****************************)
(********************************************************************************)
(* kernel u = (k_u, n)
        where u is of the form S^n k_u
        i.e., k_u is the "kernel" and n is the offset *)
val univ_kernel : universe -> ML (universe & int)

//ordering on universes:
//    constants come first, in order of their size
//    named universes come next, in lexical order of their kernels and their offsets
//    unification variables next, in lexical order of their kernels and their offsets
//    max terms come last
//e.g, [Z; S Z; S S Z; u1; S u1; u2; S u2; S S u2; ?v1; S ?v1; ?v2]
val compare_univs (u1 u2 : universe) : ML int

val eq_univs (u1 u2 : universe) : ML bool

val eq_univs_list (us vs : universes) : ML bool

(********************************************************************************)
(*********************** Utilities for computation types ************************)
(********************************************************************************)

val ml_comp (t:term) (r:range) : ML comp

val comp_effect_name (c:comp) : lident

val comp_flags (c:comp) : list cflag

val comp_eff_name_res_and_args (c:comp) : lident & typ & args

(*
 * For layered effects, given a (repr a is), return is
 * For wp effects, given a (unit -> M a wp), return wp
 *
 * The pattern matching is very syntactic inside this function
 * It is called from the computation types in the layered effect combinators
 *   e.g. f and g in bind
 * Layered effects typechecking code already makes sure that those types
 *   have this exact shape
 *)
val effect_indices_from_repr (repr:term) (is_layered:bool) (r:range) (err:string)
: ML (list term)

val destruct_comp (c:comp_typ) : ML (universe & typ & typ)

val is_named_tot (c:comp) : bool

val is_total_comp (c:comp) : ML bool

val is_partial_return (c:comp) : ML bool

val is_tot_or_gtot_comp (c:comp) : ML bool

val is_pure_effect (l:lident) : bool

val is_pure_comp (c:comp) : ML bool

val is_ghost_effect (l:lident) : bool
val is_div_effect (l:lident) : bool
val is_pure_or_ghost_comp (c:comp) : ML bool
val is_pure_or_ghost_effect (l:lident) : bool
val is_pure_or_ghost_function (t:typ) : ML bool

val head_of (t : term) : ML term
val head_and_args (t : term) : ML (term & args)  // Destructs a single Tm_app
val head_and_args_full (t : term) : ML (term & args) // Collects all Tm_app nodes
val head_and_args_full_unmeta (t : term) : ML (term & args)

val leftmost_head (t : term) : ML term

val leftmost_head_and_args (t : term) : ML (term & args)

val un_uinst (t:term) : ML term

val is_ml_comp (c:comp) : ML bool

val comp_result (c:comp) : typ

val set_result_typ (c:comp) (t:typ) : ML comp

val is_trivial_wp (c:comp) : ML bool

val comp_effect_args (c:comp) : args

(********************************************************************************)
(*               Simple utils on the structure of a term                        *)
(********************************************************************************)
val is_primop_lid : lident -> ML bool
val is_primop : term -> ML bool

val unascribe : term -> ML term

val ascribe : term -> ascription -> ML term

val unfold_lazy : lazyinfo -> ML term
val unlazy : term -> ML term
val unlazy_emb : term -> ML term
val unlazy_as_t : lazy_kind -> term -> ML 'a
val mk_lazy (t : 'a) (typ : typ) (k : lazy_kind) (r : option range) : ML term

val canon_app : term -> ML term

val unrefine : term -> ML term

val is_uvar : term -> ML bool

val is_unit : term -> ML bool

val is_eqtype_no_unrefine : term -> ML bool

val is_fun : term -> ML bool

val is_function_typ : typ -> ML bool

val pre_typ : typ -> ML typ

val destruct : typ -> lident -> ML (option args)

val lids_of_sigelt (se: sigelt) : list lident

val lid_of_sigelt (se:sigelt) : option lident

val quals_of_sigelt (x: sigelt) : list qualifier

val range_of_sigelt (x: sigelt) : range

val range_of_arg : arg -> range

val range_of_args : args -> range -> ML range

val mk_app : term -> args -> ML term

val mk_app_binders : term -> binders -> ML term

(***********************************************************************************************)
(* Combining an effect name with the name of one of its actions, or a
   data constructor name with the name of one of its formal parameters

   NOTE: the conventions defined here must be in sync with manually
   linked ML files, such as ulib/ml/prims.ml
 *)
(***********************************************************************************************)

val field_projector_prefix : string (* = "__proj__" *)

(* NOTE: the following would have been desirable:

<<
let field_projector_prefix = Ident.reserved_prefix ^ "proj__"
>>

   but it DOES NOT work with --use_hints on
   examples/preorders/MRefHeap.fst (even after regenerating hints), it
   will produce the following error:

   fstar.exe  --use_hints MRefHeap.fst
   ./MRefHeap.fst(55,51-58,27): (Error) Unknown assertion failed
   Verified module: MRefHeap (2150 milliseconds)
   1 error was reported (see above)

   In fact, any naming convention that DOES NOT start with
   Ident.reserved_prefix seems to work.
*)

val field_projector_sep : string (* = "__item__" *)

val field_projector_contains_constructor : string -> bool


val mk_field_projector_name_from_string : string -> string -> string

val mk_field_projector_name_from_ident : lident -> ident -> ML lident

val mk_field_projector_name : lident -> bv -> int -> ML lident

val ses_of_sigbundle (se:sigelt) : ML (list sigelt)

val set_uvar : uvar -> term -> ML unit

val qualifier_equal (q1 q2 : qualifier) : ML bool


(***********************************************************************************************)
(* closing types and terms *)
(***********************************************************************************************)
val abs (bs:binders) (t:term) (lopt:option residual_comp) : ML term

val arrow_ln (bs:binders) (c:comp) : ML term
val arrow (bs:binders) (c:comp) : ML term
val flat_arrow (bs:binders) (c:comp) : ML term

val canon_arrow (t:term) : ML term

val refine (b:bv) (t:term) : ML term
val branch (b:branch) : ML branch // awful name

val has_decreases (c:comp) : ML bool

(*
 * AR: this function returns the binders and comp result type of an arrow type,
 *     flattening arrows of the form t -> Tot (t1 -> C), so that it returns two binders in this example
 *     the function also descends under the refinements (e.g. t -> Tot (f:(t1 -> C){phi}))
 *)
val arrow_formals_comp_ln (k:term) : ML (binders & comp)

val arrow_formals_comp (k:term) : ML (binders & comp)
val arrow_formals_ln (k:term) : ML (binders & typ)
val arrow_formals (k:term) : ML (binders & typ)

(* let_rec_arity e f:
    if `f` is a let-rec bound name in e
    then this function returns
        1. f's type
        2. the natural arity of f, i.e., the number of arguments including universes on which the let rec is defined
        3. a list of booleans, one for each argument above, where the boolean is true iff the variable appears in the f's decreases clause
    This is used by NBE for detecting potential non-terminating loops
*)
val let_rec_arity (lb:letbinding) : ML (int & option (list bool))

val abs_formals_maybe_unascribe_body : bool -> term -> ML (binders & term & option residual_comp)

val abs_formals (t:term) : ML (binders & term & option residual_comp)

val remove_inacc (t:term) : ML term

val mk_letbinding
  (lbname : either bv fv)
  (univ_vars : list univ_name)
  (typ : term)
  (eff : lident)
  (def : term)
  (lbattrs : list term)
  (pos : range)
  : letbinding

val close_univs_and_mk_letbinding
  (recs : option (list fv))
  (lbname : either bv fv)
  (univ_vars : list univ_name)
  (typ : term)
  (eff : lident)
  (def : term)
  (attrs : list term)
  (pos : range)
  : ML letbinding

val open_univ_vars_binders_and_comp (uvs:univ_names) (bs:binders) (c:comp) : ML (univ_names & binders & comp)

(********************************************************************************)
(*********************** Various tests on constants  ****************************)
(********************************************************************************)

val is_tuple_constructor (t:typ) : bool
val is_dtuple_constructor (t:typ) : bool
val is_lid_equality (x : lident) : bool

val is_forall    : lident -> bool
val is_exists    : lident -> bool
val is_qlid      : lident -> bool

val lid_is_connective : lident -> ML bool

val is_constructor (t:term) (lid : lident) : ML bool

val is_constructed_typ (t:term) (lid : lident) : ML bool

val get_tycon : term -> ML (option term)

val is_fstar_tactics_by_tactic : term -> ML bool

(********************************************************************************)
(*********************** Constructors of common terms  **************************)
(********************************************************************************)

val ktype  : term
val ktype0 : term

//Type(u), where u is a new universe unification variable
val type_u () : ML (typ & universe)

val type_with_u (u:universe) : ML typ

val attr_substitute : term

val exp_bool (b:bool) : ML term
val exp_true_bool : term
val exp_false_bool : term
val exp_unit : term
(* Makes an (unbounded) integer from its string repr. *)
val exp_int (s:string) : ML term
val exp_char (c:FStar.Char.char) : ML term
val exp_string (s:string) : ML term

val fvar_const (l:lid) : ML term
val tand : term
val tor : term
val timp : term
val tiff : term
val t_bool : term
val b2t_v : term
val t_not : term
// These are `True` and `False`, not the booleans
val t_false : term
val t_true : term
val tac_opaque_attr : term
val tcdecltime_attr : term
val inline_let_attr : term
val rename_let_attr : term

val t_ctx_uvar_and_sust : term
val t_universe_uvar : term
val t_dsl_tac_typ : term

val mk_conj_opt (phi1 : option term) (phi2 : term) : ML (option term)
val mk_binop (op_t phi1 phi2 : term) : ML term

val mk_neg : term -> ML term
val mk_conj (phi1 phi2 : term) : ML term
val mk_conj_l (phi : list term) : ML term
val mk_disj (phi1 phi2 : term) : ML term
val mk_disj_l (phi : list term) : ML term
val mk_imp (phi1 phi2 : term) : ML term
val mk_iff (phi1 phi2 : term) : ML term

val b2t (e:term) : ML term
val unb2t (e:term) : ML (option term)

val is_t_true (t:term) : ML bool
val mk_conj_simp (t1 t2 : term) : ML term
val mk_disj_simp (t1 t2 : term) : ML term

val teq : term
val mk_untyped_eq2 (e1 e2 : term) : ML term
val mk_eq2 (u:universe) (t:typ) (e1:term) (e2:term) : ML term

val mk_eq3_no_univ (t1 t2 e1 e2 : term) : ML term

val mk_has_type (t x t' : term) : ML term

val tforall : term 
val texists : term 
val t_haseq : term 

val decidable_eq : term
val mk_decidable_eq (t e1 e2 : term) : ML term

val b_and : term

val mk_and (e1 e2 : term) : ML term
val mk_and_l (es : list term) : ML term
val mk_boolean_negation (b:term) : ML term

val mk_residual_comp (l:lident) (t: option typ) (f:list cflag) : residual_comp
val residual_tot (t:typ) : residual_comp
val residual_gtot (t:typ) : residual_comp
val residual_comp_of_comp (c:comp) : ML residual_comp

val mk_forall_no_univ (x:bv) (body:typ) : ML typ
val mk_forall (u:universe) (x:bv) (body:typ) : ML typ

val close_forall_no_univs (bs : list binder) (f : typ) : ML typ

val mk_exists_no_univ (x:bv) (body:typ) : ML typ
val mk_exists (u:universe) (x:bv) (body:typ) : ML typ

val close_exists_no_univs (bs : list binder) (f : typ) : ML typ

val if_then_else (b t1 t2 : term) : ML term

//////////////////////////////////////////////////////////////////////////////////////
// Operations on squashed and other irrelevant/sub-singleton types
//////////////////////////////////////////////////////////////////////////////////////
val mk_squash (u:universe) (p:term) : ML term

val mk_auto_squash (u:universe) (p:term) : ML term

val un_squash (t:term) : ML (option term)

val is_squash (t:term) : ML (option (universe & term))

val is_auto_squash (t:term) : ML (option (universe & term))

val is_sub_singleton (t:term) : ML bool

val arrow_one_ln (t:typ) : ML (option (binder & comp))
val arrow_one (t:typ) : ML (option (binder & comp))

val abs_one_ln (t:typ) : ML (option (binder & term))

val is_free_in (bv:bv) (t:term) : ML bool

val action_as_lb (eff_lid:lident) (a:action) (pos:range) : ML sigelt

(* Some reification utilities *)
val mk_reify (t:term) (lopt:option Ident.lident) : ML term
val mk_reflect (t:term) : ML term

(* Some utilities for clients who wish to build top-level bindings and keep
 * their delta-qualifiers correct. *)

val incr_delta_depth : delta_depth -> delta_depth

val is_unknown (t:term) : ML bool

val mk_list (typ:term) (rng:range) (l:list term) : ML term

// Checks for syntactic equality. A returned false doesn't guarantee anything.
// We DO NOT OPEN TERMS as we descend on them, and just compare their bound variable
// indices. We also ignore some parts of the syntax such universes and most annotations.

(* generic *)
val eqlist (eq : 'a -> 'a -> ML bool) (xs : list 'a) (ys : list 'a) : ML bool
val eqsum (e1 : 'a -> 'a -> ML bool) (e2 : 'b -> 'b -> ML bool) (x : either 'a 'b) (y : either 'a 'b) : ML bool
val eqprod (e1 : 'a -> 'a -> ML bool) (e2 : 'b -> 'b -> ML bool) (x : 'a & 'b) (y : 'a & 'b) : ML bool
val eqopt (e : 'a -> 'a -> ML bool) (x : option 'a) (y : option 'a) : ML bool

// Setting this ref to `true` causes messages to appear when
// some discrepancy was found. This is useful when trying to debug
// why term_eq is returning `false`. This reference is `one shot`,
// it will disable itself when term_eq returns, but in that single run
// it will provide a (backwards) trace of where the discrepancy apperared.
//
// Use at your own peril, and please keep it if there's no good
// reason against it, so I don't have to go crazy again.
val debug_term_eq : ref bool

val term_eq_dbg (dbg : bool) (t1 t2 : term) : ML bool
val eq_aqual (a1 a2 : aqual) : ML bool
val eq_bqual (b1 b2 : bqual) : ML bool
val term_eq (t1 t2 : term) : ML bool

// An estimation of the size of a term, only for debugging
val sizeof (t:term) : ML int

val is_fvar (lid:lident) (t:term) : ML bool

val is_synth_by_tactic (t:term) : ML bool

val has_attribute (attrs:list Syntax.attribute) (attr:lident) : ML bool

(* Checks whether the list of attrs contains an application of `attr`, and
 * returns the arguments if so. If there's more than one, the first one
 * takes precedence. *)
val get_attribute (attr : lident) (attrs:list Syntax.attribute) : ML (option args)

val remove_attr (attr : lident) (attrs:list attribute) : ML (list attribute)

///////////////////////////////////////////
// Setting pragmas
///////////////////////////////////////////
val process_pragma (p:pragma) (r:range) : ML unit

///////////////////////////////////////////////////////////////////////////////////////////////
val unbound_variables (tm:term) : ML (list bv)
val extract_attr' (attr_lid:lid) (attrs:list term) : ML (option (list term & args))

val extract_attr (attr_lid:lid) (se:sigelt) : ML (option (sigelt & args))

val is_lemma_comp (c:comp) : bool
val is_lemma (t:typ) : ML bool

(* Utilities for working with Lemma's decorated with SMTPat *)
val is_smt_lemma (t:term) : ML bool

val list_elements (e:term) : ML (option (list term))

val destruct_lemma_with_smt_patterns (t:term)
: ML (option (binders & term & term & list (list arg)))
//binders, pre, post, patterns

val triggers_of_smt_lemma (t:term)
: ML (list (list lident)) //for each disjunctive pattern
                            //for each conjunct
                            //triggers in a conjunt

(* Takes a term of shape `fun x -> e` and returns `e` when
`x` is not free in it. If it is free or the term
has some other shape just apply it to `()`. *)
val unthunk (t:term) : ML term

val unthunk_lemma_post (t:term) : ML term

val smt_lemma_as_forall (t:term) (universe_of_binders: binders -> ML (list universe))
: ML term

(* End SMT Lemma utilities *)


(* Effect utilities *)

(*
 * Mainly reading the combinators out of the eff_decl record
 *
 * For combinators that are present only in either wp or layered effects,
 *   their getters return option tscheme
 * Leaving it to the callers to deal with it
 *)

val effect_sig_ts (sig:effect_signature) : tscheme

val apply_eff_sig (f:tscheme -> ML tscheme) : effect_signature -> ML effect_signature

val eff_decl_of_new_effect (se:sigelt) : ML eff_decl

val is_layered (ed:eff_decl) : bool

val apply_wp_eff_combinators (f:tscheme -> ML tscheme) (combs:wp_eff_combinators) : ML wp_eff_combinators
val apply_layered_eff_combinators (f:tscheme -> ML tscheme) (combs:layered_eff_combinators) : ML layered_eff_combinators
val apply_eff_combinators (f:tscheme -> ML tscheme) (combs:eff_combinators) : ML eff_combinators

val get_layered_close_combinator (ed:eff_decl) : option tscheme
val get_wp_close_combinator (ed:eff_decl) : option tscheme
val get_eff_repr (ed:eff_decl) : option tscheme
val get_bind_vc_combinator (ed:eff_decl) : tscheme & option indexed_effect_combinator_kind
val get_return_vc_combinator (ed:eff_decl) : tscheme
val get_bind_repr (ed:eff_decl) : option tscheme

val get_return_repr (ed:eff_decl) : option tscheme
val get_wp_trivial_combinator (ed:eff_decl) : option tscheme
val get_layered_if_then_else_combinator (ed:eff_decl) : option (tscheme & option indexed_effect_combinator_kind)
val get_wp_if_then_else_combinator (ed:eff_decl) : option tscheme
val get_wp_ite_combinator (ed:eff_decl) : option tscheme
val get_stronger_vc_combinator (ed:eff_decl) : tscheme & option indexed_effect_combinator_kind
val get_stronger_repr (ed:eff_decl) : option tscheme

val aqual_is_erasable (aq:aqual) : ML bool

val is_erased_head (t:term) : ML (option (universe & term))

val apply_reveal (u:universe) (ty:term) (v:term) : ML term

val check_mutual_universes (lbs:list letbinding) : ML unit

val ctx_uvar_should_check (u:ctx_uvar) : ML should_check_uvar
val ctx_uvar_typ (u:ctx_uvar) : ML term
val ctx_uvar_typedness_deps (u:ctx_uvar) : ML (list ctx_uvar)

val flatten_refinement : term -> ML term

val contains_strictly_positive_attribute (attrs:list attribute) : ML bool

val contains_unused_attribute (attrs:list attribute) : ML bool

//retains the original attributes as is, while deciding if they contains
//the "strictly_positive" attribute
//we retain the attributes since they will then be carried in arguments
//that are applied to the corresponding binder, which is used in embeddings
//and Rel to construct binders from arguments alone
val parse_positivity_attributes (attrs:list attribute)
: ML (option positivity_qualifier & list attribute)

val encode_positivity_attributes (pqual:option positivity_qualifier) (attrs:list attribute)
: ML (list attribute)

val is_binder_strictly_positive (b:binder) : bool
val is_binder_unused (b:binder) : bool

val deduplicate_terms (l:list term) : ML (list term)

val eq_binding (b1 b2 : binding) : ML bool

(* Destruct application: head, universes, and args. *)
val hua (t:term) : ML (option (fv & list universe & args))

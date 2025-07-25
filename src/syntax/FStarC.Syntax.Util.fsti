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
open FStarC.Dyn
open FStarC.Syntax.Subst

open FStarC.Class.Show
open FStarC.Class.Monad
open FStarC.Class.Setlike

(********************************************************************************)
(**************************Utilities for identifiers ****************************)
(********************************************************************************)

(* A hook into FStarC.Syntax.Print, only for debugging and error messages.
 * The reference is set in FStarC.Main *)
val tts_f : ref (option (term -> string))
val tts (t:term) : string
val ttd_f : ref (option (term -> Pprint.document))
val ttd (t:term) : Pprint.document

val mk_discriminator (lid:lident) : lident

(* is uppercase name like Cons *)
val is_name (lid:lident) : bool

val aqual_of_binder (b:binder) : aqual

val bqual_and_attrs_of_aqual (a:aqual) : bqual & list attribute

val arg_of_non_null_binder (b:binder) : arg

val args_of_non_null_binders (binders:binders) : args

val args_of_binders (binders:Syntax.binders) : (Syntax.binders & args)

val name_binders (bs:binders) : binders

val name_function_binders (t:term) : term

val subst_of_list (formals:binders) (actuals:args) : subst_t

val rename_binders (replace_xs:binders) (with_ys:binders) : subst_t

val unmeta : term -> term
val unmeta_safe : term -> term
val unmeta_lift : term -> term

(********************************************************************************)
(*************************** Utilities for universes ****************************)
(********************************************************************************)
(* kernel u = (k_u, n)
        where u is of the form S^n k_u
        i.e., k_u is the "kernel" and n is the offset *)
val univ_kernel : universe -> universe & int

//ordering on universes:
//    constants come first, in order of their size
//    named universes come next, in lexical order of their kernels and their offsets
//    unification variables next, in lexical order of their kernels and their offsets
//    max terms come last
//e.g, [Z; S Z; S S Z; u1; S u1; u2; S u2; S S u2; ?v1; S ?v1; ?v2]
val compare_univs (u1 u2 : universe) : int

val eq_univs (u1 u2 : universe) : bool

val eq_univs_list (us vs : universes) : bool

(********************************************************************************)
(*********************** Utilities for computation types ************************)
(********************************************************************************)

val ml_comp (t:term) (r:range) : comp

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
: list term

val destruct_comp (c:comp_typ) : (universe & typ & typ)

val is_named_tot (c:comp) : bool

val is_total_comp (c:comp) : bool

val is_partial_return (c:comp) : bool

val is_tot_or_gtot_comp (c:comp) : bool

val is_pure_effect (l:lident) : bool

val is_pure_comp (c:comp) : bool

val is_ghost_effect (l:lident) : bool
val is_div_effect (l:lident) : bool
val is_pure_or_ghost_comp (c:comp) : bool
val is_pure_or_ghost_effect (l:lident) : bool
val is_pure_or_ghost_function (t:typ) : bool
val is_lemma_comp (c:comp) : bool
val is_lemma (t:typ) : bool

val head_of (t : term) : term
val head_and_args (t : term) : term & args
val head_and_args_full (t : term) : term & args
val head_and_args_full_unmeta (t : term) : term & args

val leftmost_head (t : term) : term

val leftmost_head_and_args (t : term) : term & args

val un_uinst (t:term) : term

val is_ml_comp (c:comp) : bool

val comp_result (c:comp) : typ

val set_result_typ (c:comp) (t:typ) : comp

val is_trivial_wp (c:comp) : bool

val comp_effect_args (c:comp) : args

(********************************************************************************)
(*               Simple utils on the structure of a term                        *)
(********************************************************************************)
val is_primop_lid : lident -> bool
val is_primop : term -> bool

val unascribe : term -> term

val ascribe : term -> ascription -> term

val unfold_lazy : lazyinfo -> term
val unlazy : term -> term
val unlazy_emb : term -> term
val unlazy_as_t : lazy_kind -> term -> 'a
val mk_lazy (t : 'a) (typ : typ) (k : lazy_kind) (r : option range) : term

val canon_app : term -> term

val unrefine : term -> term

val is_uvar : term -> bool

val is_unit : term -> bool

val is_eqtype_no_unrefine : term -> bool

val is_fun : term -> bool

val is_function_typ : typ -> bool

val pre_typ : typ -> typ

val destruct : typ -> lident -> option args

val lids_of_sigelt (se: sigelt) : list lident

val lid_of_sigelt (se:sigelt) : option lident

val quals_of_sigelt (x: sigelt) : list qualifier

val range_of_sigelt (x: sigelt) : range

val range_of_arg : arg -> range

val range_of_args : args -> range -> range

val mk_app : term -> args -> term

val mk_app_binders : term -> binders -> term

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

val mk_field_projector_name_from_ident : lident -> ident -> lident

val mk_field_projector_name : lident -> bv -> int -> lident

val ses_of_sigbundle (se:sigelt) :list sigelt

val set_uvar : uvar -> term -> unit

val qualifier_equal (q1 q2 : qualifier) : bool


(***********************************************************************************************)
(* closing types and terms *)
(***********************************************************************************************)
val abs (bs:binders) (t:term) (lopt:option residual_comp) : term

val arrow_ln (bs:binders) (c:comp) : term
val arrow (bs:binders) (c:comp) : term
val flat_arrow (bs:binders) (c:comp) : term

val canon_arrow (t:term) : term

val refine (b:bv) (t:term) : term
val branch (b:branch) : branch // awful name

val has_decreases (c:comp) : bool

(*
 * AR: this function returns the binders and comp result type of an arrow type,
 *     flattening arrows of the form t -> Tot (t1 -> C), so that it returns two binders in this example
 *     the function also descends under the refinements (e.g. t -> Tot (f:(t1 -> C){phi}))
 *)
val arrow_formals_comp_ln (k:term) : binders & comp

val arrow_formals_comp (k:term) : binders & comp
val arrow_formals_ln (k:term) : binders & typ
val arrow_formals (k:term) : binders & typ

(* let_rec_arity e f:
    if `f` is a let-rec bound name in e
    then this function returns
        1. f's type
        2. the natural arity of f, i.e., the number of arguments including universes on which the let rec is defined
        3. a list of booleans, one for each argument above, where the boolean is true iff the variable appears in the f's decreases clause
    This is used by NBE for detecting potential non-terminating loops
*)
val let_rec_arity (lb:letbinding) : int & option (list bool)

val abs_formals_maybe_unascribe_body : bool -> term -> binders & term & option residual_comp 

val abs_formals (t:term) : binders & term & option residual_comp

val remove_inacc (t:term) : term

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
  : letbinding

val open_univ_vars_binders_and_comp (uvs:univ_names) (bs:binders) (c:comp) : univ_names & binders & comp

(********************************************************************************)
(*********************** Various tests on constants  ****************************)
(********************************************************************************)

val is_tuple_constructor (t:typ) : bool
val is_dtuple_constructor (t:typ) : bool
val is_lid_equality (x : lident) : bool

val is_forall    : lident -> bool
val is_exists    : lident -> bool
val is_qlid      : lident -> bool

val lid_is_connective : lident -> bool

val is_constructor (t:term) (lid : lident) : bool

val is_constructed_typ (t:term) (lid : lident) : bool

val get_tycon : term -> option term

val is_fstar_tactics_by_tactic : term -> bool

(********************************************************************************)
(*********************** Constructors of common terms  **************************)
(********************************************************************************)

val ktype  : term
val ktype0 : term

//Type(u), where u is a new universe unification variable
val type_u () : typ & universe

val type_with_u (u:universe) : typ

val attr_substitute : term

val exp_bool (b:bool) : term
val exp_true_bool : term
val exp_false_bool : term
val exp_unit : term
(* Makes an (unbounded) integer from its string repr. *)
val exp_int (s:string) : term
val exp_char (c:FStar.Char.char) : term
val exp_string (s:string) : term

val fvar_const (l:lid) : term
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
val dm4f_bind_range_attr : term
val tcdecltime_attr : term
val inline_let_attr : term
val rename_let_attr : term

val t_ctx_uvar_and_sust : term
val t_universe_uvar : term
val t_dsl_tac_typ : term

val mk_conj_opt (phi1 : option term) (phi2 : term) : option term
val mk_binop (op_t phi1 phi2 : term) : term

val mk_neg : term -> term
val mk_conj (phi1 phi2 : term) : term
val mk_conj_l (phi : list term) : term
val mk_disj (phi1 phi2 : term) : term
val mk_disj_l (phi : list term) : term
val mk_imp (phi1 phi2 : term) : term
val mk_iff (phi1 phi2 : term) : term

val b2t (e:term) : term
val unb2t (e:term) : option term

val is_t_true (t:term) : bool
val mk_conj_simp (t1 t2 : term) : term
val mk_disj_simp (t1 t2 : term) : term

val teq : term
val mk_untyped_eq2 (e1 e2 : term) : term
val mk_eq2 (u:universe) (t:typ) (e1:term) (e2:term) : term

val mk_eq3_no_univ (t1 t2 e1 e2 : term) : term

val mk_has_type (t x t' : term) : term

val tforall : term 
val texists : term 
val t_haseq : term 

val decidable_eq : term
val mk_decidable_eq (t e1 e2 : term) : term

val b_and : term

val mk_and (e1 e2 : term) : term
val mk_and_l (es : list term) : term
val mk_boolean_negation (b:term) : term

val mk_residual_comp (l:lident) (t: option typ) (f:list cflag) : residual_comp
val residual_tot (t:typ) : residual_comp
val residual_gtot (t:typ) : residual_comp
val residual_comp_of_comp (c:comp) : residual_comp

val mk_forall_no_univ (x:bv) (body:typ) : typ
val mk_forall (u:universe) (x:bv) (body:typ) : typ

val close_forall_no_univs (bs : list binder) (f : typ) : typ

val mk_exists_no_univ (x:bv) (body:typ) : typ
val mk_exists (u:universe) (x:bv) (body:typ) : typ

val close_exists_no_univs (bs : list binder) (f : typ) : typ

val if_then_else (b t1 t2 : term) : term

//////////////////////////////////////////////////////////////////////////////////////
// Operations on squashed and other irrelevant/sub-singleton types
//////////////////////////////////////////////////////////////////////////////////////
val mk_squash (u:universe) (p:term) : term

val mk_auto_squash (u:universe) (p:term) : term

val un_squash (t:term) : option term

val is_squash (t:term) : option (universe & term)

val is_auto_squash (t:term) : option (universe & term)

val is_sub_singleton (t:term) : bool

val arrow_one_ln (t:typ) : option (binder & comp)
val arrow_one (t:typ) : option (binder & comp)

val abs_one_ln (t:typ) : option (binder & term)

val is_free_in (bv:bv) (t:term) : bool

val action_as_lb (eff_lid:lident) (a:action) (pos:range) : sigelt

(* Some reification utilities *)
val mk_reify (t:term) (lopt:option Ident.lident) : term
val mk_reflect (t:term) : term

(* Some utilities for clients who wish to build top-level bindings and keep
 * their delta-qualifiers correct (e.g. dmff). *)

val incr_delta_depth : delta_depth -> delta_depth

val is_unknown (t:term) : bool

val dm4f_lid (ed:eff_decl) (name:string) : lident

val mk_list (typ:term) (rng:range) (l:list term) : term

// Checks for syntactic equality. A returned false doesn't guarantee anything.
// We DO NOT OPEN TERMS as we descend on them, and just compare their bound variable
// indices. We also ignore some parts of the syntax such universes and most annotations.

// Setting this ref to `true` causes messages to appear when
// some discrepancy was found. This is useful when trying to debug
// why term_eq is returning `false`. This reference is `one shot`,
// it will disable itself when term_eq returns, but in that single run
// it will provide a (backwards) trace of where the discrepancy apperared.
//
// Use at your own peril, and please keep it if there's no good
// reason against it, so I don't have to go crazy again.
val debug_term_eq : ref bool

(* generic *)
val eqlist (eq : 'a -> 'a -> bool) (xs : list 'a) (ys : list 'a) : bool
val eqsum (e1 : 'a -> 'a -> bool) (e2 : 'b -> 'b -> bool) (x : either 'a 'b) (y : either 'a 'b) : bool
val eqprod (e1 : 'a -> 'a -> bool) (e2 : 'b -> 'b -> bool) (x : 'a & 'b) (y : 'a & 'b) : bool
val eqopt (e : 'a -> 'a -> bool) (x : option 'a) (y : option 'a) : bool

val term_eq_dbg (dbg : bool) (t1 t2 : term) : bool
val eq_aqual (a1 a2 : aqual) : bool
val eq_bqual (b1 b2 : bqual) : bool
val term_eq (t1 t2 : term) : bool

// An estimation of the size of a term, only for debugging
val sizeof (t:term) : int

val is_fvar (lid:lident) (t:term) : bool

val is_synth_by_tactic (t:term) : bool

val has_attribute (attrs:list Syntax.attribute) (attr:lident) : bool

(* Checks whether the list of attrs contains an application of `attr`, and
 * returns the arguments if so. If there's more than one, the first one
 * takes precedence. *)
val get_attribute (attr : lident) (attrs:list Syntax.attribute) : option args

val remove_attr (attr : lident) (attrs:list attribute) : list attribute

///////////////////////////////////////////
// Setting pragmas
///////////////////////////////////////////
val process_pragma (p:pragma) (r:range) : unit

///////////////////////////////////////////////////////////////////////////////////////////////
val unbound_variables (tm:term) : list bv
val extract_attr' (attr_lid:lid) (attrs:list term) : option (list term & args)

val extract_attr (attr_lid:lid) (se:sigelt) : option (sigelt & args)

(* Utilities for working with Lemma's decorated with SMTPat *)
val is_smt_lemma (t:term) : bool

val list_elements (e:term) : option (list term)

val destruct_lemma_with_smt_patterns (t:term)
: option (binders & term & term & list (list arg))
//binders, pre, post, patterns

val triggers_of_smt_lemma (t:term)
:  list (list lident) //for each disjunctive pattern
                            //for each conjunct
                            //triggers in a conjunt

(* Takes a term of shape `fun x -> e` and returns `e` when
`x` is not free in it. If it is free or the term
has some other shape just apply it to `()`. *)
val unthunk (t:term) : term

val unthunk_lemma_post (t:term) : term

val smt_lemma_as_forall (t:term) (universe_of_binders: binders -> list universe)
: term

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

val apply_eff_sig (f:tscheme -> tscheme) : effect_signature -> effect_signature

val eff_decl_of_new_effect (se:sigelt) :eff_decl

val is_layered (ed:eff_decl) : bool
val is_dm4f (ed:eff_decl) : bool

val apply_wp_eff_combinators (f:tscheme -> tscheme) (combs:wp_eff_combinators) : wp_eff_combinators
val apply_layered_eff_combinators (f:tscheme -> tscheme) (combs:layered_eff_combinators) : layered_eff_combinators
val apply_eff_combinators (f:tscheme -> tscheme) (combs:eff_combinators) : eff_combinators

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

val aqual_is_erasable (aq:aqual) : bool

val is_erased_head (t:term) : option (universe & term) 

val apply_reveal (u:universe) (ty:term) (v:term) : term

val check_mutual_universes (lbs:list letbinding) : unit

val ctx_uvar_should_check (u:ctx_uvar) : should_check_uvar
val ctx_uvar_typ (u:ctx_uvar) : term
val ctx_uvar_typedness_deps (u:ctx_uvar) : list ctx_uvar

val flatten_refinement : term -> term

val contains_strictly_positive_attribute (attrs:list attribute) : bool

val contains_unused_attribute (attrs:list attribute) : bool

//retains the original attributes as is, while deciding if they contains
//the "strictly_positive" attribute
//we retain the attributes since they will then be carried in arguments
//that are applied to the corresponding binder, which is used in embeddings
//and Rel to construct binders from arguments alone
val parse_positivity_attributes (attrs:list attribute)
: option positivity_qualifier & list attribute

val encode_positivity_attributes (pqual:option positivity_qualifier) (attrs:list attribute)
: list attribute

val is_binder_strictly_positive (b:binder) : bool
val is_binder_unused (b:binder) : bool

val deduplicate_terms (l:list term) : list term 

val eq_binding (b1 b2 : binding) : bool

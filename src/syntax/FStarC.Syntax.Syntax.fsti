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
module FStarC.Syntax.Syntax

(* Type definitions for the core AST *)

open FStarC
open FStarC.Effect
open FStarC.Range.Type
open FStarC.Ident
open FStarC.Dyn
open FStarC.Const
open FStarC.VConfig

include FStarC.Class.HasRange
open FStarC.Class.Show
open FStarC.Class.Deq
open FStarC.Class.Ord
open FStarC.Class.Tagged

(* Objects with metadata *)
[@@ PpxDerivingYoJson; PpxDerivingShow ]
type withinfo_t 'a = {
  v: 'a;
  p: range;
}

(* Free term and type variables *)
[@@ PpxDerivingYoJson; PpxDerivingShow ]
type var  = lident

(* Term language *)
[@@ PpxDerivingYoJson; PpxDerivingShow ]
type sconst = FStarC.Const.sconst

[@@ PpxDerivingYoJson; PpxDerivingShowConstant "None" ]
type memo 'a = ref (option 'a)

(* Simple types used in native compilation
 * to record the types of lazily embedded terms
 *)
type emb_typ =
  | ET_abstract
  | ET_fun  of emb_typ & emb_typ
  | ET_app  of string & list emb_typ

//versioning for unification variables
[@@ PpxDerivingYoJson; PpxDerivingShow ]
type version = {
    major:int;
    minor:int
}

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type universe =
  | U_zero
  | U_succ  of universe
  | U_max   of list universe
  | U_bvar  of int
  | U_name  of univ_name
  | U_unif  of universe_uvar
  | U_unknown
and univ_name = ident
and universe_uvar = Unionfind.p_uvar (option universe) & version & range

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type univ_names    = list univ_name

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type universes     = list universe

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type monad_name    = lident

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type quote_kind =
  | Quote_static
  | Quote_dynamic

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type maybe_set_use_range =
  | NoUseRange
  | SomeUseRange of range

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type delta_depth =
  | Delta_constant_at_level of int
  // ^ A symbol that can be unfolded n times to a term whose head is a
  // constant, e.g., nat is (Delta_constant_at_level 1) to int, level 0
  // is a literal constant.
  | Delta_equational_at_level of int
  // ^ Level 0 is a symbol that may be equated to another by
  // extensional reasoning, n > 0 can be unfolded n times to a
  // Delta_equational_at_level 0 term.
  | Delta_abstract of delta_depth
  // ^ A symbol marked abstract whose depth is the argument d.

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type should_check_uvar =
  | Allow_unresolved of string  (* Escape hatch for uvars in logical guards that are sometimes left unresolved *)
  | Allow_untyped of string     (* Escape hatch to not re-typecheck guards in WPs and types of pattern bound vars *)
  | Allow_ghost of string       (* In some cases, e.g., in ctrl_rewrite, we introduce uvars in Ghost context *)
  | Strict                      (* Strict uvar that must be typechecked *)
  | Already_checked             (* A uvar whose solution has already been checked *)

type positivity_qualifier =
  | BinderStrictlyPositive
  | BinderUnused

type term' =
  | Tm_bvar       of bv                //bound variable, referenced by de Bruijn index
  | Tm_name       of bv                //local constant, referenced by a unique name derived from bv.ppname and bv.index
  | Tm_fvar       of fv                //fully qualified reference to a top-level symbol from a module
  | Tm_uinst      of term & universes  //universe instantiation; the first argument must be one of the three constructors above
  | Tm_constant   of sconst
  | Tm_type       of universe
  | Tm_abs        {  (* fun (xi:ti) -> t : (M t' wp | N) *)
      bs:binders;
      body:term;
      rc_opt:option residual_comp
    }
  | Tm_arrow      {  (* (xi:ti) -> M t' wp *)
      bs:binders;
      comp:comp
    }
  | Tm_refine     {  (* x:t{phi} *)
      b:bv;
      phi:term
    }
  | Tm_app        {  (* h tau_1 ... tau_n, args in order from left to right *)
      hd:term;
      args:args
    }
  | Tm_match      {  (* (match e (as x returns asc)? with b1 ... bn) : (C | N)) *)
      scrutinee:term;
      ret_opt:option match_returns_ascription;
      brs:list branch;
      rc_opt:option residual_comp
    }
  | Tm_ascribed   {  (* an effect label is the third arg, filled in by the type-checker *)
      tm:term;
      asc:ascription;
      eff_opt:option lident
    }
  | Tm_let        {  (* let (rec?) x1 = e1 AND ... AND xn = en in e *)
      lbs:letbindings;
      body:term
    }
  | Tm_uvar       of ctx_uvar_and_subst  (* A unification variable ?u (aka meta-variable)
                                            and a delayed substitution of only NM or NT elements *)
  | Tm_delayed    {  (* A delayed substitution --- always force it; never inspect it directly *)
      tm:term;
      substs:subst_ts
    }
  | Tm_meta       {  (* Some terms carry metadata, for better code generation, SMT encoding etc. *)
      tm:term;
      meta:metadata
    }
  | Tm_lazy       of lazyinfo                                    (* A lazily encoded term *)
  | Tm_quoted     of term & quoteinfo                            (* A quoted term, in one of its many variants *)
  | Tm_unknown                                                   (* only present initially while desugaring a term *)
and ctx_uvar = {                                                 (* (G |- ?u : t), a uvar introduced in context G at type t *)
  ctx_uvar_head:uvar;                                          (* ?u *)
  ctx_uvar_gamma:gamma;                                        (* G: a cons list of bindings (most recent at the head) *)
  ctx_uvar_binders:binders;                                    (* All the Tm_name bindings in G, a snoc list (most recent at the tail) *)
  ctx_uvar_reason:string;
  ctx_uvar_range:range;
  ctx_uvar_meta: option ctx_uvar_meta_t;
}
and ctx_uvar_meta_t =
  | Ctx_uvar_meta_tac of term
  | Ctx_uvar_meta_attr of term (* An attribute associated with an implicit argument using the #[@@@ defer_to ...] notation *)
and ctx_uvar_and_subst = ctx_uvar & subst_ts

and uvar_decoration = {
  uvar_decoration_typ:typ;
  uvar_decoration_typedness_depends_on:list ctx_uvar;
  uvar_decoration_should_check:should_check_uvar;
  uvar_decoration_should_unrefine:bool;
}

and uvar = Unionfind.p_uvar (option term & uvar_decoration) & version & range
and uvars = FlatSet.t ctx_uvar
and match_returns_ascription = binder & ascription               (* as x returns C|t *)
and branch = pat & option term & term                           (* optional when clause in each branch *)
and ascription = either term comp & option term & bool        (* e <: t [by tac] or e <: C [by tac] *)
                                                                 (* the bool says whether the ascription is an equality ascription, i.e. $: *)
and pat' =
  | Pat_constant of sconst
  | Pat_cons     of fv & option universes & list (pat & bool)    (* flag marks an explicitly provided implicit *)
  | Pat_var      of bv                                           (* a pattern bound variable (linear in a pattern) *)
  | Pat_dot_term of option term                                  (* dot patterns: determined by other elements in the pattern *)
                                                                 (* the option term is the optionally resolved pat dot term *)
and letbinding = {  //let f : forall u1..un. M t = e
    lbname :lbname;          // f
    lbunivs:list univ_name;  // u1..un
    lbtyp  :typ;             // t
    lbeff  :lident;          // M
    lbdef  :term;            // e
    lbattrs:list attribute;  // attrs
    lbpos  :range;           // original position of 'e'
}
and antiquotations = int & list term
and quoteinfo = {
    qkind          : quote_kind;
    antiquotations : antiquotations;
(*************************************************************************
  ANTIQUOTATIONS and shifting

 The antiquotations of a quoted term (Tm_quoted) are kept in the
 antiquotations list above. The terms inside that list are not scoped by
 any binder *inside* the quoted term, but are affected by substitutions
 on the full term as usual. Inside the quoted terms, the points where
 antiquotations are spliced in Tm_bvar nodes, where the index of the
 bv indexes into the antiquotations list above, where the rightmost
 elements is closer in scope. I.e., a term like

   Tm_quoted (Tm_bvar 2, {antiquotations = [a;b;c]})

 is really just `a`. This makes the representation of antiquotations
 more canonical (we previously had freshly-named Tm_names instead).

 Unembedding a Tm_quoted(tm, aq) term will simply take tm and substitute
 it appropriately with the information from aq. Every antiquotation must
 be a literal term for this to work, and not a variable or an expression
 computing a quoted term.

 When extracting or encoding a quoted term to SMT, then, we cannot
 simply unembed as the antiquotations are most likely undetermined. For
 instance, the extraction of a term like

   Tm_quoted(1 + bvar 0, aq = [ compute_some_term() ]}

 should be something like

   pack_ln (Tv_App (pack_ln (Tv_App (plus, Tv_Const 1)), compute_some_term()).

 To implement this conveniently, we allow _embedding_ terms with
 antiquotations, so we can implement extraction basically by:

   extract (Tm_quoted (Tm_bvar i, aq)) =
     aq `index` (length aq - 1 - i)

   extract (Tm_quoted (t, aq)) =
     let tv = inspect_ln t in
     let tv_e = embed_term_view tv aq in
     let t' = mk_app pack_ln tv_e in
     extract t'

 That is, unfolding one level of the view, enclosing it with a
 pack_ln call, and recursing. For this to work, however, we need the
 antiquotations to be preserved, hence we pass them to embed_term_view.
 The term_view embedding will also take care of *shifting* the
 antiquotations (see the int there) when traversing a binder in the
 quoted term. Hence, a term like:

   Tm_quoted (fun x -> 1 + x + bvar 1, aqs = [t]),

 will be unfolded to

   Tv_Abs (x, Tm_quoted(1 + bvar0 + bvar1, aqs = [t], shift=1))

 where the shift is needed to make the bvar1 actually point to t.

*************************************************************************)
}
and comp_typ = {
  comp_univs:universes;
  effect_name:lident;
  result_typ:typ;
  effect_args:args;
  flags:list cflag
}
and comp' =
  | Total  of typ
  | GTotal of typ
  | Comp   of comp_typ
and term = syntax term'
and typ = term                                                   (* sometimes we use typ to emphasize that a term is a type *)
and pat = withinfo_t pat'
and comp = syntax comp'
and arg = term & aqual                                           (* marks an explicitly provided implicit arg *)
and args = list arg
and binder = {
  binder_bv    : bv;
  binder_qual  : bqual;
  binder_positivity : option positivity_qualifier;
  binder_attrs : list attribute
}                                                                (* f:   #[@@ attr] n:nat -> vector n int -> T; f #17 v *)
and binders = list binder                                       (* bool marks implicit binder *)
and decreases_order =
  | Decreases_lex of list term  (* a decreases clause may either specify a lexicographic ordered list of terms, *)
  | Decreases_wf of term & term  (* or a well-founded relation and a term *)
and cflag =                                                      (* flags applicable to computation types, usually for optimizations *)
  | TOTAL                                                          (* computation has no real effect, can be reduced safely *)
  | MLEFFECT                                                       (* the effect is ML    (Parser.Const.effect_ML_lid) *)
  | LEMMA                                                          (* the effect is Lemma (Parser.Const.effect_Lemma_lid) *)
  | RETURN                                                         (* the WP is return_wp of something *)
  | PARTIAL_RETURN                                                 (* the WP is return_wp of something, possibly strengthened with some precondition *)
  | SOMETRIVIAL                                                    (* the WP is the null wp *)
  | TRIVIAL_POSTCONDITION                                          (* the computation has no meaningful postcondition *)
  | SHOULD_NOT_INLINE                                              (* a stopgap, see issue #1362, removing it revives the failure *)
  | CPS                                                            (* computation is marked with attribute `cps`, for DM4F, seems useless, see #1557 *)
  | DECREASES of decreases_order
and metadata =
  | Meta_pattern       of list term & list args                  (* Patterns for SMT quantifier instantiation; the first arg instantiation *)
  | Meta_named         of lident                                 (* Useful for pretty printing to keep the type abbreviation around *)
  | Meta_labeled       of list Pprint.document & range & bool    (* Sub-terms in a VC are labeled with error messages to be reported, used in SMT encoding *)
  | Meta_desugared     of meta_source_info                       (* Node tagged with some information about source term before desugaring *)
  | Meta_monadic       of monad_name & typ                       (* Annotation on a Tm_app or Tm_let node in case it is monadic for m not in {Pure, Ghost, Div} *)
                                                                 (* Contains the name of the monadic effect and  the type of the subterm *)
  | Meta_monadic_lift  of monad_name & monad_name & typ          (* Sub-effecting: lift the subterm of type typ *)
                                                                 (* from the first monad_name m1 to the second monad name m2 *)
and meta_source_info =
  | Sequence                                    (* used when resugaring *)
  | Primop                                      (* ... add more cases here as needed for better code generation *)
  | Masked_effect
  | Meta_smt_pat
  | Machine_integer of signedness & width
and fv_qual =
  | Data_ctor
  | Record_projector of (lident & ident)        (* the fully qualified (unmangled) name of the data constructor and the field being projected *)
  | Record_ctor of lident & list ident         (* the type of the record being constructed and its (unmangled) fields in order *)
  | Unresolved_projector of option fv          (* ToSyntax's best guess at what the projector is (based only on scoping rules) *)
  | Unresolved_constructor of unresolved_constructor (* ToSyntax's best guess at what the constructor is (based only on scoping rules) *)
and unresolved_constructor = {
  uc_base_term : bool;      // The base term is `e` when the user writes `{ e with f1=v1; ... }`
  uc_typename: option lident; // The constructed type, as determined by the ToSyntax's scoping rules
  uc_fields : list lident  // The fields names as written in the source
}
and lbname = either bv fv
and letbindings = bool & list letbinding        (* let recs may have more than one element; top-level lets have lidents *)
                                                (* boolean true indicates rec *)
and subst_ts = list (list subst_elt)            (* A composition of parallel substitutions *)
             & maybe_set_use_range              (* and a maybe range update, Some r, to set the use_range of subterms to r.def_range *)
and subst_elt =
   | DB of int & bv                            (* DB i bv: replace a bound variable with index i with name bv                 *)
   | DT of int & term                          (* DT i t: replace a bound variable with index i for term *)
   | NM of bv  & int                           (* NM x i: replace a local name with a bound variable i                       *)
   | NT of bv  & term                          (* NT x t: replace a local name with a term t                                 *)
   | UN of int & universe                      (* UN u v: replace universes variable u with universe term v                  *)
   | UD of univ_name & int                     (* UD x i: replace universe name x with de Bruijn index i                     *)
and freenames = FlatSet.t bv
and syntax 'a = {
    n:'a;
    pos:range;
    vars:memo free_vars;
    hash_code:memo FStarC.Hash.hash_code
}
and bv = {
    ppname:ident;  //programmer-provided name for pretty-printing
    index:int;     //de Bruijn index 0-based, counting up from the binder
    sort:term
}
and fv = {
    fv_name :var;
    fv_qual :option fv_qual
}
and free_vars = {
    free_names      : FlatSet.t bv;
    free_uvars      : uvars;
    free_univs      : FlatSet.t universe_uvar;
    free_univ_names : FlatSet.t univ_name; //fifo
}

(* Residual of a computation type after typechecking *)
and residual_comp = {
    residual_effect:lident;                (* first component is the effect name *)
    residual_typ   :option typ;           (* second component: result type *)
    residual_flags :list cflag            (* third component: contains (an approximation of) the cflags *)
}

and attribute = term

and lazyinfo = {
    blob  : dyn;
    lkind : lazy_kind;
    ltyp  : typ;
    rng   : range;
}
// Different kinds of lazy terms. These are used to decide the unfolding
// function, instead of keeping the closure inside the lazy node, since
// that means we cannot have equality on terms (not serious) nor call
// output_value on them (serious).
and lazy_kind =
  | BadLazy
  | Lazy_bv
  | Lazy_namedv
  | Lazy_binder
  | Lazy_optionstate
  | Lazy_fvar
  | Lazy_comp
  | Lazy_env
  | Lazy_proofstate
  | Lazy_goal
  | Lazy_sigelt
  | Lazy_uvar
  | Lazy_letbinding
  | Lazy_embedding of emb_typ & Thunk.t term
  | Lazy_universe
  | Lazy_universe_uvar
  | Lazy_issue
  | Lazy_ident
  | Lazy_doc
  | Lazy_extension of string
  | Lazy_tref
and binding =
  | Binding_var      of bv
  | Binding_lid      of lident & (univ_names & typ)
  (* ^ Not a tscheme: the universe names must be taken
   * as fixed (and opened in the type). This is important since
   * we do not support universe-polymorphic recursion.
   * See #2106. *)
  | Binding_univ     of univ_name
and tscheme = list univ_name & typ
and gamma = list binding
and binder_qualifier =
  | Implicit of bool //boolean marks an inaccessible implicit argument of a data constructor
  | Meta of term     //meta-argument that specifies a tactic term
  | Equality
and bqual = option binder_qualifier
and arg_qualifier = {
  aqual_implicit : bool;
  aqual_attributes : list attribute
}
and aqual = option arg_qualifier

type pragma =
  | ShowOptions
  | SetOptions of string
  | ResetOptions of option string
  | PushOptions of option string
  | PopOptions
  | RestartSolver
  | PrintEffectsGraph  //#print-effects-graph dumps the current effects graph in a dot file named "effects.graph"
  | Check of term

instance val showable_pragma : showable pragma

type freenames_l = list bv
type formula = typ
type formulae = list typ

type qualifier =
  | Assumption                             //no definition provided, just a declaration
  | New                                    //a fresh type constant, distinct from all prior type constructors
  | Private                                //name is invisible outside the module
  | Unfold_for_unification_and_vcgen       //a definition that *should* always be unfolded by the normalizer
  | Irreducible                            //a definition that can never be unfolded by the normalizer
  | Inline_for_extraction                  //a symbol whose definition must be unfolded when compiling the program
  | NoExtract                              // a definition whose contents won't be extracted (currently, by KaRaMeL only)
  | Noeq                                   //for this type, don't generate HasEq
  | Unopteq                                //for this type, use the unoptimized HasEq scheme
  | TotalEffect                            //an effect that forbids non-termination
  | Logic                                  //a symbol whose intended usage is in the refinement logic
  | Reifiable
  | Reflectable of lident                  // with fully qualified effect name

  //the remaining qualifiers are internal: the programmer cannot write them
  | Visible_default                        //a definition that may be unfolded by the normalizer, but only if necessary (default)
  | Discriminator of lident                //discriminator for a datacon l
  | Projector of lident & ident            //projector for datacon l's argument x
  | RecordType of (list ident & list ident)          //record type whose namespace is fst and unmangled field names are snd
  | RecordConstructor of (list ident & list ident)   //record constructor whose namespace is fst and unmangled field names are snd
  | Action of lident                       //action of some effect
  | ExceptionConstructor                   //a constructor of Prims.exn
  | HasMaskedEffect                        //a let binding that may have a top-level effect
  | Effect                                 //qualifier on a name that corresponds to an effect constructor
  | OnlyName                               //qualifier internal to the compiler indicating a dummy declaration which
                                           //is present only for name resolution and will be elaborated at typechecking
  | InternalAssumption                     //an assumption internally generated by F*, e.g. hasEq axioms, not to be reported with --report_assumes

instance val ord_qualifier : ord qualifier

(* Checks if the qualifer is internal, and should not be written by users. *)
val is_internal_qualifier (q:qualifier) : bool

type tycon = lident & binders & typ                   (* I (x1:t1) ... (xn:tn) : t *)
type monad_abbrev = {
  mabbrev:lident;
  parms:binders;
  def:typ
  }

//
// Kind of a binder in an indexed effect combinator
//
type indexed_effect_binder_kind =
  | Type_binder
  | Substitutive_binder
  | BindCont_no_abstraction_binder  // a g computation (the continuation) binder in bind that's not abstracted over x:a
  | Range_binder
  | Repr_binder
  | Ad_hoc_binder
instance val showable_indexed_effect_binder_kind : showable indexed_effect_binder_kind
instance val tagged_indexed_effect_binder_kind : tagged indexed_effect_binder_kind

//
// Kind of an indexed effect combinator
//
// Substitutive invariant applies only to subcomp and ite combinators,
//   where the effect indices of the two computations could be the same,
//   and hence bound only once in the combinator definitions
//
type indexed_effect_combinator_kind =
  | Substitutive_combinator of list indexed_effect_binder_kind
  | Substitutive_invariant_combinator
  | Ad_hoc_combinator
instance val showable_indexed_effect_combinator_kind : showable indexed_effect_combinator_kind
instance val tagged_indexed_effect_combinator_kind : tagged indexed_effect_combinator_kind

type sub_eff = {
  source:lident;
  target:lident;
  lift_wp:option tscheme;
  lift:option tscheme;
  kind:option indexed_effect_combinator_kind
 }

type action = {
    action_name:lident;
    action_unqualified_name: ident; // necessary for effect redefinitions, this name shall not contain the name of the effect
    action_univs:univ_names;
    action_params : binders;
    action_defn:term;
    action_typ: typ
}

(*
 * Effect combinators for wp-based effects
 *
 * This includes both primitive effects (such as PURE, DIV)
 *   as well as user-defined DM4F effects
 *
 * repr, return_repr, and bind_repr are optional, and are set only for reifiable effects
 *
 * For DM4F effects, ret_wp, bind_wp, and other wp combinators are derived and populated by the typechecker
 *   These fields are dummy ts ([], Tm_unknown) after desugaring
 *
 * We could add another boolean, elaborated somewhere
 *)

type wp_eff_combinators = {
  ret_wp       : tscheme;
  bind_wp      : tscheme;
  stronger     : tscheme;
  if_then_else : tscheme;
  ite_wp       : tscheme;
  close_wp     : tscheme;
  trivial      : tscheme;

  repr         : option tscheme;
  return_repr  : option tscheme;
  bind_repr    : option tscheme
}


(*
 * Layered effects combinators
 *
 * All of these have pairs of type schemes,
 *   where the first component is the term ts and the second component is the type ts
 *
 * Before typechecking the effect declaration, the second component is a dummy ts
 *   In other words, desugaring sets the first component only, and typechecker then fills up the second one
 *
 * Additionally, bind, subcomp, and if_then_else have a combinator kind,
 *   this is also set to None in desugaring and set during typechecking the effect
 *
 * The close combinator is optional
 *   If it is not provided as part of the effect declaration,
 *   the typechecker also does not synthesize it (unlike if-then-else and subcomp)
 *)
type layered_eff_combinators = {
  l_repr         : (tscheme & tscheme);
  l_return       : (tscheme & tscheme);
  l_bind         : (tscheme & tscheme & option indexed_effect_combinator_kind);
  l_subcomp      : (tscheme & tscheme & option indexed_effect_combinator_kind);
  l_if_then_else : (tscheme & tscheme & option indexed_effect_combinator_kind);
  l_close        : option (tscheme & tscheme)
}

type eff_combinators =
  | Primitive_eff of wp_eff_combinators
  | DM4F_eff of wp_eff_combinators
  | Layered_eff of layered_eff_combinators

type effect_signature =
  | Layered_eff_sig of int & tscheme  // (n, ts) where n is the number of effect parameters (all upfront) in the effect signature
  | WP_eff_sig of tscheme

//
// For primitive and DM4F effects, this is set in ToSyntax
// For indexed effects, typechecker sets it (in TcEffect)
//
type eff_extraction_mode =
  | Extract_none of string  // Effect cannot be extracted
  | Extract_reify           // Effect can be extracted with reification
  | Extract_primitive       // Effect is primitive

instance val showable_eff_extraction_mode : showable eff_extraction_mode
instance val tagged_eff_extraction_mode : tagged eff_extraction_mode

(*
  new_effect {
    STATE_h (heap:Type) : result:Type -> wp:st_wp_h heap result -> Effect
    with return ....
  }
*)
type eff_decl = {
  mname           : lident;      // STATE_h

  cattributes     : list cflag;

  univs           : univ_names;  // u#heap
  binders         : binders;     // (heap:Type u#heap), univs and binders are in the scope of the rest of the combinators

  signature       : effect_signature;

  combinators     : eff_combinators;

  actions         : list action;

  eff_attrs       : list attribute;

  extraction_mode : eff_extraction_mode;
}


type sig_metadata = {
    sigmeta_active:bool;
    sigmeta_fact_db_ids:list string;
    sigmeta_admit:bool; //An internal flag to record that a sigelt's SMT proof should be admitted
                        //Used in DM4Free
    sigmeta_spliced:bool;
    sigmeta_already_checked:bool;
    // ^ This sigelt was created from a splice_t with a proof of well-typing,
    // and does not need to be checked again.
    sigmeta_extension_data: list (string & dyn) //each extension can register some data with a sig
}


type open_kind =                                          (* matters only for resolving names with some module qualifier *)
| Open_module                                             (* only opens the module, not the namespace *)
| Open_namespace  

type ident_alias = option ident

(** A restriction imposed on a `open` or `include` declaration. *)
type restriction = 
     (** No restriction, the entire module is opened or included. *)
     | Unrestricted
     (** Only a specific subset of the exported definition of a module is opened or included. *)
     | AllowList of list (ident & ident_alias)

type open_module_or_namespace = (lident & open_kind & restriction)      (* lident fully qualified name, already resolved. *)
type module_abbrev = (ident & lident)                     (* module X = A.B.C, where A.B.C is fully qualified and already resolved *)

(*
 * AR: we no longer have Sig_new_effect_for_free
 *     Sig_new_effect, with an eff_decl that has DM4F_eff combinators, with dummy wps plays its part
 *)
type sigelt' =
  | Sig_inductive_typ  {  //type l forall u1..un. (x1:t1) ... (xn:tn) : t
      lid:lident;
      us:univ_names;                    //u1..un
      params:binders;                   //(x1:t1) ... (xn:tn)
      num_uniform_params:option int;    //number of recursively uniform type parameters
      t:typ;                            //t
      mutuals:list lident;              //mutually defined types
      ds:list lident;                   //data constructors for this type
      injective_type_params:bool        //is this type injective in its type parameters?
    }
(* a datatype definition is a Sig_bundle of all mutually defined `Sig_inductive_typ`s and `Sig_datacon`s.
   perhaps it would be nicer to let this have a 2-level structure, e.g. list list sigelt,
   where each higher level list represents one of the inductive types and its constructors.
   However, the current order is convenient as it matches the type-checking order for the mutuals;
   i.e., all the type constructors first; then all the data which may refer to the type constructors *)
  | Sig_bundle  {
      ses:list sigelt;    //the set of mutually defined type and data constructors
      lids:list lident;    //all the inductive types and data constructor names in this bundle
    }
  | Sig_datacon        {
      lid:lident;             //name of the datacon
      us:univ_names;          //universe variables of the inductive type it belongs to
      t:typ;                  //the constructor's type as an arrow (including parameters)
      ty_lid:lident;          //the inductive type of the value this constructs
      num_ty_params:int;        //and the number of parameters of the inductive
      mutuals:list lident;    //mutually defined types
      injective_type_params:bool;   //is this type injective in its type parameters?
      proj_disc_lids : list lident; // the lids of the discriminators and projectors to come for this constructor
    }
  | Sig_declare_typ     {
      lid:lident;
      us:univ_names;
      t:typ
    }
  | Sig_let             {
      lbs:letbindings;
      lids:list lident;    //mutually defined
    }
  | Sig_assume          {
      lid:lident;
      us:univ_names;
      phi:formula;
    }
  | Sig_new_effect      of eff_decl
  | Sig_sub_effect      of sub_eff
  | Sig_effect_abbrev   {
      lid:lident;
      us:univ_names;
      bs:binders;
      comp:comp;
      cflags:list cflag;
    }
  | Sig_pragma          of pragma
  | Sig_splice          {
      is_typed:bool;  // true indicates a typed splice that does not re-typecheck the generated sigelt
                      // it is an experimental feature added as part of the meta DSL framework
      lids:list lident;
      tac:term;
    }

  | Sig_polymonadic_bind     {  //(m, n) |> p, the polymonadic term, and its type
      m_lid:lident;
      n_lid:lident;
      p_lid:lident;
      tm:tscheme;
      typ:tscheme;
      kind:option indexed_effect_combinator_kind;
    }
  | Sig_polymonadic_subcomp  {  //m <: n, the polymonadic subcomp term, and its type
      m_lid:lident;
      n_lid:lident;
      tm:tscheme;
      typ:tscheme;
      kind:option indexed_effect_combinator_kind;
    }
  | Sig_fail                 {
      errs:list int;      // Expected errors (empty for 'any')
      rng: range;   // range of the `expect_failure`, for error reporting
      fail_in_lax:bool;   // true if should fail in --lax
      ses:list sigelt;    // The sigelts to be checked
  }

and sigelt = {
    sigel:    sigelt';
    sigrng:   range;
    sigquals: list qualifier;
    sigmeta:  sig_metadata;
    sigattrs: list attribute;
    sigopens_and_abbrevs: list (either open_module_or_namespace module_abbrev);
    sigopts:  option vconfig; (* Saving the option context where this sigelt was checked in *)
}


type sigelts = list sigelt

type modul = {
  name: lident;
  declarations: sigelts;
  is_interface:bool;
}

val on_antiquoted : (term -> term) -> quoteinfo -> quoteinfo

(* Requires that bv.index is in scope for the antiquotation list. *)
val lookup_aq : bv -> antiquotations -> term

// This is set in FStarC.Main.main, where all modules are in-scope.
val lazy_chooser : ref (option (lazy_kind -> lazyinfo -> term))

val mod_name: modul -> lident

type path = list string
type subst_t = list subst_elt

val withinfo: 'a -> range -> withinfo_t 'a

(* Constructors for each term form; NO HASH CONSING; just makes all the auxiliary data at each node *)
val mk: 'a -> range -> syntax 'a

val mk_lb :         (lbname & list univ_name & lident & typ & term & list attribute & range) -> letbinding
val default_sigmeta: sig_metadata
val mk_sigelt:      sigelt' -> sigelt // FIXME check uses
val mk_Tm_app:      term -> args -> range -> term

(* This raises an exception if the term is not a Tm_fvar,
 * use with care. It has to be an Tm_fvar *immediately*,
 * there is no solving of Tm_delayed nor Tm_uvar. If it's
 * possible that it is not a Tm_fvar, which can be the case
 * for non-typechecked terms, just use `mk`. *)
val mk_Tm_uinst:    term -> universes -> term

val extend_app:     term -> arg -> range -> term
val extend_app_n:   term -> args -> range -> term
val mk_Tm_delayed:  (term & subst_ts) -> range -> term
val mk_Total:       typ -> comp
val mk_GTotal:      typ -> comp
val mk_Tac :        typ -> comp
val mk_Comp:        comp_typ -> comp
val bv_to_tm:       bv -> term
val bv_to_name:     bv -> term
val binders_to_names: binders -> list term

val bv_eq:           bv -> bv -> bool
val order_bv:        bv -> bv -> int
val range_of_lbname: lbname -> range
val range_of_bv:     bv -> range
val set_range_of_bv: bv -> range -> bv
val order_univ_name: univ_name -> univ_name -> int

val tun:      term
val teff:     term
val is_teff:  term -> bool
val is_type:  term -> bool

val freenames_of_binders: binders -> freenames
val binders_of_freenames: freenames -> binders
val binders_of_list:      list bv -> binders

val null_bv:        term -> bv
val mk_binder_with_attrs
           :        bv -> bqual -> option positivity_qualifier -> list attribute -> binder
val mk_binder:      bv -> binder
val null_binder:    term -> binder
val as_arg:         term -> arg
val imp_tag:        binder_qualifier
val iarg:           term -> arg
val is_null_bv:     bv -> bool
val is_null_binder: binder -> bool
val argpos:         arg -> range
val pat_bvs:        pat -> list bv
val is_bqual_implicit:    bqual -> bool
val is_aqual_implicit:    aqual -> bool
val is_bqual_implicit_or_meta: bqual -> bool
val as_bqual_implicit:    bool -> bqual
val as_aqual_implicit:    bool -> aqual
val is_top_level:   list letbinding -> bool

(* gensym *)
val freshen_bv       : bv -> bv
val freshen_binder   : binder -> binder
val gen_bv           : string -> option range -> typ -> bv
val gen_bv'          : ident -> option range -> typ -> bv
val new_bv           : option range -> typ -> bv
val new_univ_name    : option range -> univ_name
val lid_and_dd_as_fv : lident -> option fv_qual -> fv
val lid_as_fv        : lident -> option fv_qual -> fv
val fv_to_tm         : fv -> term
val fvar_with_dd     : lident -> option fv_qual -> term
val fvar             : lident -> option fv_qual -> term
val fv_eq            : fv -> fv -> bool
val fv_eq_lid        : fv -> lident -> bool
val range_of_fv      : fv -> range
val lid_of_fv        : fv -> lid
val set_range_of_fv  : fv -> range -> fv

(* attributes *)
val has_simple_attribute: list term -> string -> bool

val eq_pat : pat -> pat -> bool

///////////////////////////////////////////////////////////////////////
//Some common constants
///////////////////////////////////////////////////////////////////////
val delta_constant  : delta_depth
val delta_equational: delta_depth
val fvconst         : lident -> fv
val tconst          : lident -> term
val tabbrev         : lident -> term
val tdataconstr     : lident -> term
val t_unit          : term
val t_bool          : term
val t_int           : term
val t_string        : term
val t_exn           : term
val t_real          : term
val t_float         : term
val t_char          : term
val t_range         : term
val t___range       : term
val t_vconfig       : term
val t_norm_step     : term
val t_term          : term
val t_term_view     : term
val t_order         : term
val t_decls         : term
val t_binder        : term
val t_bv            : term
val t_tac_of        : term -> term -> term
val t_tactic_of     : term -> term
val t_tactic_unit   : term
val t_list_of       : term -> term
val t_option_of     : term -> term
val t_tuple2_of     : term -> term -> term
val t_tuple3_of     : term -> term -> term -> term
val t_tuple4_of     : term -> term -> term -> term -> term
val t_tuple5_of     : term -> term -> term -> term -> term -> term
val t_either_of     : term -> term -> term
val t_sealed_of     : term -> term
val t_erased_of     : term -> term

val unit_const_with_range : range -> term
val unit_const            : term

(** Checks wether an identity `id` is allowed by a include/open
restriction `r`. If it is not allowed,
`is_ident_allowed_by_restriction id r` returns `None`, otherwise it
returns `Some renamed`, where `renamed` is either `id` (when no there
is no `as` clause) or another identity pointing to the actual source
identity in the source module.

For example, if we have `open Foo { my_type as the_type }`,
`is_ident_allowed_by_restriction <the_type> <{ my_type as the_type }>`
will return `Some <my_type>`.
*)
val is_ident_allowed_by_restriction: ident -> restriction -> option ident

instance val has_range_syntax #a : unit -> Tot (hasRange (syntax a))
instance val has_range_withinfo #a : unit -> Tot (hasRange (withinfo_t a))
instance val has_range_sigelt : hasRange sigelt
instance val hasRange_fv : hasRange fv
instance val hasRange_bv     : hasRange bv
instance val hasRange_binder : hasRange binder
instance val hasRange_ctx_uvar : hasRange ctx_uvar

instance val showable_fv : showable fv
instance val showable_emb_typ : showable emb_typ
instance val showable_delta_depth : showable delta_depth
instance val showable_should_check_uvar : showable should_check_uvar

instance val showable_lazy_kind : showable lazy_kind

instance val showable_restriction: showable restriction
instance val showable_unresolved_constructor : showable unresolved_constructor
instance val showable_fv_qual : showable fv_qual

instance val deq_lazy_kind   : deq lazy_kind
instance val deq_bv          : deq bv
instance val deq_ident       : deq ident
instance val deq_fv          : deq lident
instance val deq_univ_name   : deq univ_name
instance val deq_delta_depth : deq delta_depth

instance val ord_bv         : ord bv
instance val ord_ident      : ord ident
instance val ord_fv         : ord lident

instance val tagged_term : tagged term
instance val tagged_sigelt : tagged sigelt

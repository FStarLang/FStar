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
module FStar.Syntax.Syntax
open FStar.ST
open FStar.All
(* Type definitions for the core AST *)

(* Prims is used for bootstrapping *)
open Prims
open FStar
open FStar.Util
open FStar.Range
open FStar.Ident
open FStar.Dyn

// JP: all these types are defined twice and every change has to be performed
// twice (because of the .fs). TODO: move the type definitions into a standalone
// fs without fsi, and move the helpers into syntaxhelpers.fs / syntaxhelpers.fsi

(* Objects with metadata *)
type withinfo_t<'a> = {
  v: 'a;
  p: Range.range;
}

(* Free term and type variables *)
type var  = withinfo_t<lident>
(* Term language *)
type sconst = FStar.Const.sconst

type pragma =
  | SetOptions of string
  | ResetOptions of option<string>
  | PushOptions of option<string>
  | PopOptions
  | LightOff

type memo<'a> = ref<option<'a>>

(* Simple types used in native compilation
 * to record the types of lazily embedded terms
 *)
type emb_typ =
  | ET_abstract
  | ET_fun  of emb_typ * emb_typ
  | ET_app  of string * list<emb_typ>

//versioning for unification variables
type version = {
    major:int;
    minor:int
}
type universe =
  | U_zero
  | U_succ  of universe
  | U_max   of list<universe>
  | U_bvar  of int
  | U_name  of univ_name
  | U_unif  of universe_uvar
  | U_unknown
and univ_name = ident
and universe_uvar = Unionfind.p_uvar<option<universe>> * version

type univ_names    = list<univ_name>
type universes     = list<universe>
type monad_name    = lident

type quote_kind =
  | Quote_static
  | Quote_dynamic

type maybe_set_use_range =
  | NoUseRange
  | SomeUseRange of range

type delta_depth =
  | Delta_constant_at_level of int    //A symbol that can be unfolded n types to a term whose head is a constant, e.g., nat is (Delta_unfoldable 1) to int, level 0 is a constant
  | Delta_equational_at_level of int  //level 0 is a symbol that may be equated to another by extensional reasoning, n > 0 can be unfolded n times to a Delta_equational_at_level 0 term
  | Delta_abstract of delta_depth   //A symbol marked abstract whose depth is the argument d

type should_check_uvar =
  | Allow_unresolved      (* Escape hatch for uvars in logical guards that are sometimes left unresolved *)
  | Allow_untyped         (* Escape hatch to not re-typecheck guards in WPs and types of pattern bound vars *)
  | Strict                (* Everything else is strict *)

type term' =
  | Tm_bvar       of bv                //bound variable, referenced by de Bruijn index
  | Tm_name       of bv                //local constant, referenced by a unique name derived from bv.ppname and bv.index
  | Tm_fvar       of fv                //fully qualified reference to a top-level symbol from a module
  | Tm_uinst      of term * universes  //universe instantiation; the first argument must be one of the three constructors above
  | Tm_constant   of sconst
  | Tm_type       of universe
  | Tm_abs        of binders*term*option<residual_comp>          (* fun (xi:ti) -> t : (M t' wp | N) *)
  | Tm_arrow      of binders * comp                              (* (xi:ti) -> M t' wp *)
  | Tm_refine     of bv * term                                   (* x:t{phi} *)
  | Tm_app        of term * args                                 (* h tau_1 ... tau_n, args in order from left to right *)
  | Tm_match      of term * list<branch>                         (* match e with b1 ... bn *)
  | Tm_ascribed   of term * ascription * option<lident>          (* an effect label is the third arg, filled in by the type-checker *)
  | Tm_let        of letbindings * term                          (* let (rec?) x1 = e1 AND ... AND xn = en in e *)
  | Tm_uvar       of ctx_uvar_and_subst                          (* A unification variable ?u (aka meta-variable)
                                                                   and a delayed substitution of only NM or NT elements *)
  | Tm_delayed    of (term * subst_ts)
                   * memo<term>                                  (* A delayed substitution --- always force it; never inspect it directly *)
  | Tm_meta       of term * metadata                             (* Some terms carry metadata, for better code generation, SMT encoding etc. *)
  | Tm_lazy       of lazyinfo                                    (* A lazily encoded term *)
  | Tm_quoted     of term * quoteinfo                            (* A quoted term, in one of its many variants *)
  | Tm_unknown                                                   (* only present initially while desugaring a term *)
and ctx_uvar = {                                                 (* (G |- ?u : t), a uvar introduced in context G at type t *)
    ctx_uvar_head:uvar;                                          (* ?u *)
    ctx_uvar_gamma:gamma;                                        (* G: a cons list of bindings (most recent at the head) *)
    ctx_uvar_binders:binders;                                    (* All the Tm_name bindings in G, a snoc list (most recent at the tail) *)
    ctx_uvar_typ:typ;                                            (* t *)
    ctx_uvar_reason:string;
    ctx_uvar_should_check:should_check_uvar;
    ctx_uvar_range:Range.range
}
and ctx_uvar_and_subst = ctx_uvar * subst_ts
and uvar = Unionfind.p_uvar<option<term>> * version
and uvars = set<ctx_uvar>
and branch = pat * option<term> * term                           (* optional when clause in each branch *)
and ascription = either<term, comp> * option<term>               (* e <: t [by tac] or e <: C [by tac] *)
and pat' =
  | Pat_constant of sconst
  | Pat_cons     of fv * list<(pat * bool)>                      (* flag marks an explicitly provided implicit *)
  | Pat_var      of bv                                           (* a pattern bound variable (linear in a pattern) *)
  | Pat_wild     of bv                                           (* need stable names for even the wild patterns *)
  | Pat_dot_term of bv * term                                    (* dot patterns: determined by other elements in the pattern and type *)
and letbinding = {  //let f : forall u1..un. M t = e
    lbname :lbname;          //f
    lbunivs:list<univ_name>; //u1..un
    lbtyp  :typ;             //t
    lbeff  :lident;          //M
    lbdef  :term;            //e
    lbattrs:list<attribute>; //attrs
    lbpos  :range;           //original position of 'e'
}
and antiquotations = list<(bv * bool * term)>
and quoteinfo = {
    qkind      : quote_kind;
    antiquotes : antiquotations;
}
and comp_typ = {
  comp_univs:universes;
  effect_name:lident;
  result_typ:typ;
  effect_args:args;
  flags:list<cflags>
}
and comp' =
  | Total  of typ * option<universe>
  | GTotal of typ * option<universe>
  | Comp   of comp_typ
and term = syntax<term'>
and typ = term                                                   (* sometimes we use typ to emphasize that a term is a type *)
and pat = withinfo_t<pat'>
and comp = syntax<comp'>
and arg = term * aqual                                           (* marks an explicitly provided implicit arg *)
and args = list<arg>
and binder = bv * aqual                                          (* f:   #n:nat -> vector n int -> T; f #17 v *)
and binders = list<binder>                                       (* bool marks implicit binder *)
and cflags =
  | TOTAL
  | MLEFFECT
  | RETURN
  | PARTIAL_RETURN
  | SOMETRIVIAL
  | TRIVIAL_POSTCONDITION
  | SHOULD_NOT_INLINE
  | LEMMA
  | CPS
  | DECREASES of term
and metadata =
  | Meta_pattern       of list<args>                             (* Patterns for SMT quantifier instantiation *)
  | Meta_named         of lident                                 (* Useful for pretty printing to keep the type abbreviation around *)
  | Meta_labeled       of string * Range.range * bool            (* Sub-terms in a VC are labeled with error messages to be reported, used in SMT encoding *)
  | Meta_desugared     of meta_source_info                       (* Node tagged with some information about source term before desugaring *)
  | Meta_monadic       of monad_name * typ                       (* Annotation on a Tm_app or Tm_let node in case it is monadic for m not in {Pure, Ghost, Div} *)
                                                                 (* Contains the name of the monadic effect and  the type of the subterm *)
  | Meta_monadic_lift  of monad_name * monad_name * typ          (* Sub-effecting: lift the subterm of type typ *)
                                                                 (* from the first monad_name m1 to the second monad name  m2 *)
and meta_source_info =
  | Sequence
  | Primop                                      (* ... add more cases here as needed for better code generation *)
  | Masked_effect
  | Meta_smt_pat
  | Mutable_alloc
  | Mutable_rval
and fv_qual =
  | Data_ctor
  | Record_projector of (lident * ident)          (* the fully qualified (unmangled) name of the data constructor and the field being projected *)
  | Record_ctor of lident * list<ident>         (* the type of the record being constructed and its (unmangled) fields in order *)
and lbname = either<bv, fv>
and letbindings = bool * list<letbinding>       (* let recs may have more than one element; top-level lets have lidents *)
and subst_ts = list<list<subst_elt>>            (* A composition of parallel substitutions *)
             * maybe_set_use_range              (* and a maybe range update, Some r, to set the use_range of subterms to r.def_range *)
and subst_elt =
   | DB of int * bv                            (* DB i t: replace a bound variable with index i with name bv                 *)
   | NM of bv  * int                           (* NM x i: replace a local name with a bound variable i                       *)
   | NT of bv  * term                          (* NT x t: replace a local name with a term t                                 *)
   | UN of int * universe                      (* UN u v: replace universes variable u with universe term v                  *)
   | UD of univ_name * int                     (* UD x i: replace universe name x with de Bruijn index i                     *)
and freenames = set<bv>
and syntax<'a> = {
    n:'a;
    pos:Range.range;
    vars:memo<free_vars>;
}
and bv = {
    ppname:ident;  //programmer-provided name for pretty-printing
    index:int;     //de Bruijn index 0-based, counting up from the binder
    sort:term
}
and fv = {
    fv_name :var;
    fv_delta:delta_depth;
    fv_qual :option<fv_qual>
}
and free_vars = {
    free_names:list<bv>;
    free_uvars:list<ctx_uvar>;
    free_univs:list<universe_uvar>;
    free_univ_names:list<univ_name>; //fifo
}

(* Residual of a computation type after typechecking *)
and residual_comp = {
    residual_effect:lident;                (* first component is the effect name *)
    residual_typ   :option<typ>;           (* second component: result type *)
    residual_flags :list<cflags>           (* third component: contains (an approximation of) the cflags *)
}

and attribute = term

and lazyinfo = {
    blob  : dyn;
    lkind : lazy_kind;
    ltyp  : typ;
    rng   : Range.range;
}
// Different kinds of lazy terms. These are used to decide the unfolding
// function, instead of keeping the closure inside the lazy node, since
// that means we cannot have equality on terms (not serious) nor call
// output_value on them (serious).
and lazy_kind =
  | BadLazy
  | Lazy_bv
  | Lazy_binder
  | Lazy_fvar
  | Lazy_comp
  | Lazy_env
  | Lazy_proofstate
  | Lazy_sigelt
  | Lazy_uvar
  | Lazy_embedding of emb_typ * FStar.Common.thunk<term>
and binding =
  | Binding_var      of bv
  | Binding_lid      of lident * tscheme
  | Binding_univ     of univ_name
and tscheme = list<univ_name> * typ
and gamma = list<binding>
and arg_qualifier =
  | Implicit of bool //boolean marks an inaccessible implicit argument of a data constructor
  | Meta of term
  | Equality
and aqual = option<arg_qualifier>

type lcomp = { //a lazy computation
    eff_name: lident;
    res_typ: typ;
    cflags: list<cflags>;
    comp_thunk: ref<(either<(unit -> comp), comp>)>
}

val on_antiquoted : (term -> term) -> quoteinfo -> quoteinfo
val lookup_aq : bv -> antiquotations -> option<(bool * term)>

// This is set in FStar.Main.main, where all modules are in-scope.
val lazy_chooser : ref<option<(lazy_kind -> lazyinfo-> term)>>
type freenames_l = list<bv>
type formula = typ
type formulae = list<typ>
val new_bv_set: unit -> set<bv>
val new_fv_set: unit -> set<lident>
val new_universe_names_set: unit -> set<univ_name>

type qualifier =
  | Assumption                             //no definition provided, just a declaration
  | New                                    //a fresh type constant, distinct from all prior type constructors
  | Private                                //name is invisible outside the module
  | Unfold_for_unification_and_vcgen       //a definition that *should* always be unfolded by the normalizer
  | Visible_default                        //a definition that may be unfolded by the normalizer, but only if necessary (default)
  | Irreducible                            //a definition that can never be unfolded by the normalizer
  | Abstract                               //a symbol whose definition is only visible within the defining module
  | Inline_for_extraction                  //a symbol whose definition must be unfolded when compiling the program
  | NoExtract                              // a definition whose contents won't be extracted (currently, by KreMLin only)
  | Noeq                                   //for this type, don't generate HasEq
  | Unopteq                                //for this type, use the unoptimized HasEq scheme
  | TotalEffect                            //an effect that forbids non-termination
  | Logic                                  //a symbol whose intended usage is in the refinement logic
  | Reifiable
  | Reflectable of lident                  // with fully qualified effect name
  //the remaining qualifiers are internal: the programmer cannot write them
  | Discriminator of lident                //discriminator for a datacon l
  | Projector of lident * ident            //projector for datacon l's argument x
  | RecordType of (list<ident> * list<ident>)          //record type whose namespace is fst and unmangled field names are snd
  | RecordConstructor of (list<ident> * list<ident>)   //record constructor whose namespace is fst and unmangled field names are snd
  | Action of lident                       //action of some effect
  | ExceptionConstructor                   //a constructor of Prims.exn
  | HasMaskedEffect                        //a let binding that may have a top-level effect
  | Effect                                 //qualifier on a name that corresponds to an effect constructor
  | OnlyName                               //qualifier internal to the compiler indicating a dummy declaration which
                                           //is present only for name resolution and will be elaborated at typechecking

type tycon = lident * binders * typ                   (* I (x1:t1) ... (xn:tn) : t *)
type monad_abbrev = {
  mabbrev:lident;
  parms:binders;
  def:typ
  }
type sub_eff = {
  source:lident;
  target:lident;
  lift_wp:option<tscheme>;
  lift:option<tscheme>
 }

(*
  new_effect {
    STATE_h (heap:Type) : result:Type -> wp:st_wp_h heap result -> Effect
    with return ....
  }
*)
type action = {
    action_name:lident;
    action_unqualified_name: ident; // necessary for effect redefinitions, this name shall not contain the name of the effect
    action_univs:univ_names;
    action_params : binders;
    action_defn:term;
    action_typ: typ
}
type eff_decl = {
    cattributes :list<cflags>;     // default cflags
    mname       :lident;           //STATE_h
    univs       :univ_names;       //initially empty; but after type-checking and generalization, usually the universe of the result type etc.
    binders     :binders;          //heap:Type
    signature   :term;             //: result:Type ... -> Effect
    ret_wp      :tscheme;          //the remaining fields ... one for each element of the interface
    bind_wp     :tscheme;
    if_then_else:tscheme;
    ite_wp      :tscheme;
    stronger    :tscheme;
    close_wp    :tscheme;
    assert_p    :tscheme;
    assume_p    :tscheme;
    null_wp     :tscheme;
    trivial     :tscheme;
    //NEW FIELDS
    //representation of the effect as pure type
    repr        :term;
    //operations on the representation
    return_repr :tscheme;
    bind_repr   :tscheme;
    //actions for the effect
    actions     :list<action>;
    eff_attrs   :list<attribute>;
}

type sig_metadata = {
    sigmeta_active:bool;
    sigmeta_fact_db_ids:list<string>;
}

// JP/NS:
//    the n-tuples hinder readability, make it difficult to maintain code (see
//    lids_of_sigelt in syntax/util.fs) and do not help being familiar with the
//    code.
//    In particular, because of tuples, everytime one needs to extend a Sig_*,
//    one needs to modify > 30 different places in the code that pattern-match
//    on a fixed-length tuple.
//    Using a record for the arguments of Sig_datacons etc. would help a bit.
//    But, given F*'s poor syntax for record arguments, this would require writing
//    (Sig_inductive_typ ({...})) which is also painful, particularly since omitting
//    the extra parentheses would not be caught by the F# parser during development.
type sigelt' =
  | Sig_inductive_typ  of lident                   //type l forall u1..un. (x1:t1) ... (xn:tn) : t
                       * univ_names                //u1..un
                       * binders                   //(x1:t1) ... (xn:tn)
                       * typ                       //t
                       * list<lident>              //mutually defined types
                       * list<lident>              //data constructors for this type
(* a datatype definition is a Sig_bundle of all mutually defined `Sig_inductive_typ`s and `Sig_datacon`s.
   perhaps it would be nicer to let this have a 2-level structure, e.g. list<list<sigelt>>,
   where each higher level list represents one of the inductive types and its constructors.
   However, the current order is convenient as it matches the type-checking order for the mutuals;
   i.e., all the type constructors first; then all the data which may refer to the type constructors *)
  | Sig_bundle         of list<sigelt>              //the set of mutually defined type and data constructors
                       * list<lident>               //all the inductive types and data constructor names in this bundle
  | Sig_datacon        of lident
                       * univ_names                 //universe variables of the inductive type it belongs to
                       * typ
                       * lident                     //the inductive type of the value this constructs
                       * int                        //and the number of parameters of the inductive
                       * list<lident>               //mutually defined types
  | Sig_declare_typ    of lident
                       * univ_names
                       * typ
  | Sig_let            of letbindings
                       * list<lident>               //mutually defined
  | Sig_main           of term
  | Sig_assume         of lident
                       * univ_names
                       * formula
  | Sig_new_effect     of eff_decl
  | Sig_new_effect_for_free of eff_decl
  | Sig_sub_effect     of sub_eff
  | Sig_effect_abbrev  of lident
                       * univ_names
                       * binders
                       * comp
                       * list<cflags>
  | Sig_pragma         of pragma
  | Sig_splice         of list<lident> * term

and sigelt = {
    sigel:    sigelt';
    sigrng:   Range.range;
    sigquals: list<qualifier>;
    sigmeta:  sig_metadata;
    sigattrs: list<attribute>
}

type sigelts = list<sigelt>

type modul = {
  name: lident;
  declarations: sigelts;
  exports: sigelts;
  is_interface:bool;
}
val mod_name: modul -> lident

type path = list<string>
type subst_t = list<subst_elt>
type mk_t_a<'a> = option<unit> -> range -> syntax<'a>
type mk_t = mk_t_a<term'>

val contains_reflectable:  list<qualifier> -> bool

val withsort: 'a -> withinfo_t<'a>
val withinfo: 'a -> Range.range -> withinfo_t<'a>

(* Constructors for each term form; NO HASH CONSING; just makes all the auxiliary data at each node *)
val mk: 'a -> Tot<mk_t_a<'a>>

val mk_lb :         (lbname * list<univ_name> * lident * typ * term * range) -> letbinding
val default_sigmeta: sig_metadata
val mk_sigelt:      sigelt' -> sigelt // FIXME check uses
val mk_Tm_app:      term -> args -> Tot<mk_t>
val mk_Tm_uinst:    term -> universes -> term
val extend_app:     term -> arg -> Tot<mk_t>
val extend_app_n:   term -> args -> Tot<mk_t>
val mk_Tm_delayed:  (term * subst_ts) -> Range.range -> term
val mk_Total:       typ -> comp
val mk_GTotal:      typ -> comp
val mk_Total':      typ -> option<universe> -> comp
val mk_GTotal':     typ -> option<universe> -> comp
val mk_Comp:        comp_typ -> comp
val mk_lcomp:
    eff_name: lident ->
    res_typ: typ ->
    cflags: list<cflags> ->
    comp_thunk: (unit -> comp) -> lcomp
val lcomp_comp: lcomp -> comp
val bv_to_tm:       bv -> term
val bv_to_name:     bv -> term

val bv_eq:           bv -> bv -> Tot<bool>
val order_bv:        bv -> bv -> Tot<int>
val range_of_lbname: lbname -> range
val range_of_bv:     bv -> range
val set_range_of_bv: bv -> range -> bv
val order_univ_name: univ_name -> univ_name -> int

val tun:      term
val teff:     term
val is_teff:  term -> bool
val is_type:  term -> bool

val no_names:          freenames
val no_universe_names: set<univ_name>
val no_fvars:          set<lident>

val freenames_of_list:    list<bv> -> freenames
val freenames_of_binders: binders -> freenames
val list_of_freenames:    freenames -> list<bv>
val binders_of_freenames: freenames -> binders
val binders_of_list:      list<bv> -> binders

val null_bv:        term -> bv
val mk_binder:      bv -> binder
val null_binder:    term -> binder
val as_arg:         term -> arg
val imp_tag:        arg_qualifier
val iarg:           term -> arg
val is_null_bv:     bv -> bool
val is_null_binder: binder -> bool
val argpos:         arg -> Range.range
val pat_bvs:        pat -> list<bv>
val is_implicit:    aqual -> bool
val as_implicit:    bool -> aqual
val is_top_level:   list<letbinding> -> bool

(* gensym *)
val next_id:        (unit -> int)
val reset_gensym:   (unit -> unit)
val freshen_bv:     bv -> bv
val freshen_binder:  binder -> binder
val gen_bv:         string -> option<Range.range> -> typ -> bv
val new_bv:         option<range> -> typ -> bv
val new_univ_name:  option<range> -> univ_name
val lid_as_fv:      lident -> delta_depth -> option<fv_qual> -> fv
val fv_to_tm:       fv -> term
val fvar:           lident -> delta_depth -> option<fv_qual> -> term
val fv_eq:          fv -> fv -> bool
val fv_eq_lid:      fv -> lident -> bool
val range_of_fv:    fv -> range
val lid_of_fv:      fv -> lid
val set_range_of_fv:fv -> range -> fv

(* attributes *)
val has_simple_attribute: list<term> -> string -> bool

val eq_pat : pat -> pat -> bool

///////////////////////////////////////////////////////////////////////
//Some common constants
///////////////////////////////////////////////////////////////////////
module C = FStar.Parser.Const
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
val t_float         : term
val t_char          : term
val t_range         : term
val t_norm_step     : term
val t_term          : term
val t_order         : term
val t_decls         : term
val t_binder        : term
val t_bv            : term
val t_tactic_unit   : term
val t_tac_unit      : term
val t_list_of       : term -> term
val t_option_of     : term -> term
val t_tuple2_of     : term -> term -> term
val unit_const      : term

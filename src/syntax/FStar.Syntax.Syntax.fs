(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or impliedmk_
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
open FStar.Const
open FStar.Dyn
module PC = FStar.Parser.Const

(* Objects with metadata *)
// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
type withinfo_t<'a> = {
  v:  'a;
  p: Range.range;
}

(* Free term and type variables *)
// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
type var = withinfo_t<lident>

(* Term language *)
// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
type sconst = FStar.Const.sconst

// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
type pragma =
  | SetOptions of string
  | ResetOptions of option<string>
  | PushOptions of option<string>
  | PopOptions
  | LightOff

// IN F*: [@ PpxDerivingYoJson (PpxDerivingShowConstant "None") ]
type memo<'a> = ref<option<'a>>

//versioning for unification variables
// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
type version = {
    major:int;
    minor:int
}

// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
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


// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
type univ_names    = list<univ_name>

// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
type universes     = list<universe>

// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
type monad_name    = lident

// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
type quote_kind =
  | Quote_static
  | Quote_dynamic

// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
type maybe_set_use_range =
  | NoUseRange
  | SomeUseRange of range

// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
type delta_depth =
  | Delta_constant_at_level of int    //A symbol that can be unfolded n types to a term whose head is a constant, e.g., nat is (Delta_unfoldable 1) to int, level 0 is a constant
  | Delta_equational_at_level of int  //level 0 is a symbol that may be equated to another by extensional reasoning, n > 0 can be unfolded n times to a Delta_equational_at_level 0 term
  | Delta_abstract of delta_depth   //A symbol marked abstract whose depth is the argument d

// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
// Different kinds of lazy terms. These are used to decide the unfolding
// function, instead of keeping the closure inside the lazy node, since
// that means we cannot have equality on terms (not serious) nor call
// output_value on them (serious).
type lazy_kind =
  | BadLazy
  | Lazy_bv
  | Lazy_binder
  | Lazy_fvar
  | Lazy_comp
  | Lazy_env
  | Lazy_proofstate
  | Lazy_sigelt
  | Lazy_uvar

// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
type should_check_uvar =
  | Allow_unresolved      (* Escape hatch for uvars in logical guards that are sometimes left unresolved *)
  | Allow_untyped         (* Escape hatch to not re-typecheck guards in WPs and types of pattern bound vars *)
  | Strict                (* Everything else is strict *)

// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
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
    typ   : typ;
    rng   : Range.range;
}
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

// This is set in FStar.Main.main, where all modules are in-scope.
let lazy_chooser : ref<option<(lazy_kind -> lazyinfo -> term)>> = mk_ref None

let mk_lcomp eff_name res_typ cflags comp_thunk =
    { eff_name = eff_name;
      res_typ = res_typ;
      cflags = cflags;
      comp_thunk = FStar.Util.mk_ref (Inl comp_thunk) }
let lcomp_comp lc =
    match !(lc.comp_thunk) with
    | Inl thunk ->
      let c = thunk () in
      lc.comp_thunk := Inr c;
      c
    | Inr c -> c

type freenames_l = list<bv>
type formula = typ
type formulae = list<typ>
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
  | TotalEffect                            //an effect that forbis non-termination
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

type action = {
    action_name:lident;
    action_unqualified_name: ident; // necessary for effect redefinitions, this name shall not contain the name of the effect
    action_univs:univ_names;
    action_params : binders;
    action_defn:term;
    action_typ: typ
}
type eff_decl = {
    cattributes :list<cflags>;
    mname       :lident;
    univs       :univ_names;
    binders     :binders;
    signature   :term;
    ret_wp      :tscheme;
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
  is_interface:bool
}
let mod_name (m: modul) = m.name

type path = list<string>
type subst_t = list<subst_elt>
type mk_t_a<'a> = option<unit> -> range -> syntax<'a>
type mk_t = mk_t_a<term'>


let contains_reflectable (l: list<qualifier>): bool =
    Util.for_some (function Reflectable _ -> true | _ -> false) l

(*********************************************************************************)
(* Identifiers to/from strings *)
(*********************************************************************************)
let withinfo v r = {v=v; p=r}
let withsort v = withinfo v dummyRange

let bv_eq (bv1:bv) (bv2:bv) = bv1.ppname.idText=bv2.ppname.idText && bv1.index=bv2.index
let order_bv x y =
  let i = String.compare x.ppname.idText y.ppname.idText in
  if i = 0
  then x.index - y.index
  else i

let order_fv x y = String.compare x.str y.str

let range_of_lbname (l:lbname) = match l with
    | Inl x -> x.ppname.idRange
    | Inr fv -> range_of_lid fv.fv_name.v
let range_of_bv x = x.ppname.idRange
let set_range_of_bv x r = {x with ppname=Ident.mk_ident(x.ppname.idText, r)}


(* Helpers *)
let on_antiquoted (f : (term -> term)) (qi : quoteinfo) : quoteinfo =
    let aq = List.map (fun (bv, b, t) -> (bv, b, f t)) qi.antiquotes in
    { qi with antiquotes = aq }

let lookup_aq (bv : bv) (aq : antiquotations) : option<(bool * term)> =
    match List.tryFind (fun (bv', _, _) -> bv_eq bv bv') aq with
    | Some (_, b, e) -> Some (b, e)
    | None -> None

(*********************************************************************************)
(* Syntax builders *)
(*********************************************************************************)
open FStar.Range

let syn p k f = f k p
let mk_fvs () = Util.mk_ref None
let mk_uvs () = Util.mk_ref None
let new_bv_set () : set<bv> = Util.new_set order_bv
let new_fv_set () :set<lident> = Util.new_set order_fv
let order_univ_name x y = String.compare (Ident.text_of_id x) (Ident.text_of_id y)
let new_universe_names_set () : set<univ_name> = Util.new_set order_univ_name

let no_names  = new_bv_set()
let no_fvars  = new_fv_set()
let no_universe_names = new_universe_names_set ()
//let memo_no_uvs = Util.mk_ref (Some no_uvs)
//let memo_no_names = Util.mk_ref (Some no_names)
let freenames_of_list l = List.fold_right Util.set_add l no_names
let list_of_freenames (fvs:freenames) = Util.set_elements fvs

(* Constructors for each term form; NO HASH CONSING; just makes all the auxiliary data at each node *)
let mk (t:'a) = fun (_:option<unit>) r -> {
    n=t;
    pos=r;
    vars=Util.mk_ref None;
}
let bv_to_tm   bv :term = mk (Tm_bvar bv) None (range_of_bv bv)
let bv_to_name bv :term = mk (Tm_name bv) None (range_of_bv bv)
let mk_Tm_app (t1:typ) (args:list<arg>) (k:option<unit>) p =
    match args with
    | [] -> t1
    | _ -> mk (Tm_app (t1, args)) None p
let mk_Tm_uinst (t:term) = function
    | [] -> t
    | us ->
      match t.n with
        | Tm_fvar _ ->  mk (Tm_uinst(t, us)) None t.pos
        | _ -> failwith "Unexpected universe instantiation"

let extend_app_n t args' kopt r = match t.n with
    | Tm_app(head, args) -> mk_Tm_app head (args@args') kopt r
    | _ -> mk_Tm_app t args' kopt r
let extend_app t arg kopt r = extend_app_n t [arg] kopt r
let mk_Tm_delayed lr pos : term = mk (Tm_delayed(lr, Util.mk_ref None)) None pos
let mk_Total' t  u: comp  = mk (Total(t, u)) None t.pos
let mk_GTotal' t u: comp = mk (GTotal(t, u)) None t.pos
let mk_Total t = mk_Total' t None
let mk_GTotal t = mk_GTotal' t None
let mk_Comp (ct:comp_typ) : comp  = mk (Comp ct) None ct.result_typ.pos
let mk_lb (x, univs, eff, t, e, pos) = {
    lbname=x;
    lbunivs=univs;
    lbtyp=t;
    lbeff=eff;
    lbdef=e;
    lbattrs=[];
    lbpos=pos;
  }

let default_sigmeta = { sigmeta_active=true; sigmeta_fact_db_ids=[] }
let mk_sigelt (e: sigelt') = { sigel = e; sigrng = Range.dummyRange; sigquals=[]; sigmeta=default_sigmeta; sigattrs = [] }
let mk_subst (s:subst_t)   = s
let extend_subst x s : subst_t = x::s
let argpos (x:arg) = (fst x).pos

let tun : term = mk (Tm_unknown) None dummyRange
let teff : term = mk (Tm_constant Const_effect) None dummyRange
let is_teff (t:term) = match t.n with
    | Tm_constant Const_effect -> true
    | _ -> false
let is_type (t:term) = match t.n with
    | Tm_type _ -> true
    | _ -> false
let null_id  = mk_ident("_", dummyRange)
let null_bv k = {ppname=null_id; index=0; sort=k}
let mk_binder (a:bv) : binder = a, None
let null_binder t : binder = null_bv t, None
let imp_tag = Implicit false
let iarg t : arg = t, Some imp_tag
let as_arg t : arg = t, None
let is_null_bv (b:bv) = b.ppname.idText = null_id.idText
let is_null_binder (b:binder) = is_null_bv (fst b)

let is_top_level = function
    | {lbname=Inr _}::_ -> true
    | _ -> false

let freenames_of_binders (bs:binders) : freenames =
    List.fold_right (fun (x, _) out -> Util.set_add x out) bs no_names

let binders_of_list fvs : binders = (fvs |> List.map (fun t -> t, None))
let binders_of_freenames (fvs:freenames) = Util.set_elements fvs |> binders_of_list
let is_implicit = function Some (Implicit _) -> true | _ -> false
let as_implicit = function true -> Some imp_tag | _ -> None

let pat_bvs (p:pat) : list<bv> =
    let rec aux b p = match p.v with
        | Pat_dot_term _
        | Pat_constant _ -> b
        | Pat_wild x
        | Pat_var x -> x::b
        | Pat_cons(_, pats) -> List.fold_left (fun b (p, _) -> aux b p) b pats
    in
  List.rev <| aux [] p

(* Gen sym *)
let gen_reset =
    let x = Util.mk_ref 0 in
    let gen () = incr x; !x in
    let reset () = x := 0 in
    gen, reset
let next_id = fst gen_reset
let reset_gensym = snd gen_reset
let range_of_ropt = function
    | None -> dummyRange
    | Some r -> r
let gen_bv : string -> option<Range.range> -> typ -> bv = fun s r t ->
  let id = mk_ident(s, range_of_ropt r) in
  {ppname=id; index=next_id(); sort=t}
let new_bv ropt t = gen_bv Ident.reserved_prefix ropt t

let freshen_bv bv =
    if is_null_bv bv
    then new_bv (Some (range_of_bv bv)) bv.sort
    else {bv with index=next_id()}
let freshen_bvs bvs = List.map freshen_bv bvs

let freshen_binder (b:binder) = let (bv, aq) = b in (freshen_bv bv, aq)
let freshen_binders bs = List.map freshen_binder bs

let new_univ_name ropt =
    let id = next_id() in
    mk_ident (Ident.reserved_prefix ^ Util.string_of_int id, range_of_ropt ropt)
let mkbv x y t  = {ppname=x;index=y;sort=t}
let lbname_eq l1 l2 = match l1, l2 with
  | Inl x, Inl y -> bv_eq x y
  | Inr l, Inr m -> lid_equals l m
  | _ -> false
let fv_eq fv1 fv2 = lid_equals fv1.fv_name.v fv2.fv_name.v
let fv_eq_lid fv lid = lid_equals fv.fv_name.v lid
let set_bv_range bv r = {bv with ppname=mk_ident(bv.ppname.idText, r)}
let lid_as_fv l dd dq : fv = {
    fv_name=withinfo l (range_of_lid l);
    fv_delta=dd;
    fv_qual =dq;
}
let fv_to_tm (fv:fv) : term = mk (Tm_fvar fv) None (range_of_lid fv.fv_name.v)
let fvar l dd dq =  fv_to_tm (lid_as_fv l dd dq)
let lid_of_fv (fv:fv) = fv.fv_name.v
let range_of_fv (fv:fv) = range_of_lid (lid_of_fv fv)
let set_range_of_fv (fv:fv) (r:Range.range) =
    {fv with fv_name={fv.fv_name with v=Ident.set_lid_range (lid_of_fv fv) r}}
let has_simple_attribute (l: list<term>) s =
  List.existsb (function
    | { n = Tm_constant (Const_string (data, _)) } when data = s ->
        true
    | _ ->
        false
  ) l

// Compares the SHAPE of the patterns, *ignoring bound variables*
let rec eq_pat (p1 : pat) (p2 : pat) : bool =
    match p1.v, p2.v with
    | Pat_constant c1, Pat_constant c2 -> eq_const c1 c2
    | Pat_cons (fv1, as1), Pat_cons (fv2, as2) ->
        if fv_eq fv1 fv2
        then begin assert(List.length as1 = List.length as2);
                   List.zip as1 as2 |>
                   List.for_all (fun ((p1, b1), (p2, b2)) -> b1 = b2 && eq_pat p1 p2)
             end
        else false
    | Pat_var _, Pat_var _ -> true
    | Pat_wild _, Pat_wild _ -> true
    | Pat_dot_term (bv1, t1), Pat_dot_term (bv2, t2) -> true //&& term_eq t1 t2
    | _, _ -> false

///////////////////////////////////////////////////////////////////////
//Some common constants
///////////////////////////////////////////////////////////////////////
let delta_constant = Delta_constant_at_level 0
let delta_equational = Delta_equational_at_level 0
let tconst l = mk (Tm_fvar(lid_as_fv l delta_constant None)) None Range.dummyRange
let tabbrev l = mk (Tm_fvar(lid_as_fv l (Delta_constant_at_level 1) None)) None Range.dummyRange
let tdataconstr l = fv_to_tm (lid_as_fv l delta_constant (Some Data_ctor))
let t_unit      = tconst PC.unit_lid
let t_bool      = tconst PC.bool_lid
let t_int       = tconst PC.int_lid
let t_string    = tconst PC.string_lid
let t_float     = tconst PC.float_lid
let t_char      = tabbrev PC.char_lid
let t_range     = tconst PC.range_lid
let t_term      = tconst PC.term_lid
let t_order     = tconst PC.order_lid
let t_decls     = tabbrev PC.decls_lid
let t_binder    = tconst PC.binder_lid
let t_binders   = tconst PC.binders_lid
let t_bv        = tconst PC.bv_lid
let t_fv        = tconst PC.fv_lid
let t_norm_step = tconst PC.norm_step_lid
let t_tactic_unit = mk_Tm_app (mk_Tm_uinst (tabbrev PC.tactic_lid) [U_zero]) [as_arg t_unit] None Range.dummyRange
let t_tac_unit    = mk_Tm_app (mk_Tm_uinst (tabbrev PC.u_tac_lid) [U_zero]) [as_arg t_unit] None Range.dummyRange
let t_list_of t = mk_Tm_app (mk_Tm_uinst (tabbrev PC.list_lid) [U_zero]) [as_arg t] None Range.dummyRange
let t_option_of t = mk_Tm_app (mk_Tm_uinst (tabbrev PC.option_lid) [U_zero]) [as_arg t] None Range.dummyRange
let t_tuple2_of t1 t2 = mk_Tm_app (mk_Tm_uinst (tabbrev PC.lid_tuple2) [U_zero;U_zero]) [as_arg t1; as_arg t2] None Range.dummyRange
let unit_const = mk (Tm_constant FStar.Const.Const_unit) None Range.dummyRange

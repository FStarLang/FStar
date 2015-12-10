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
(* Type definitions for the core AST *)

(* Prims is used for bootstrapping *)
open Prims
open FStar
open FStar.Util
open FStar.Range
open FStar.Ident

exception Err of string
exception Error of string * Range.range
exception Warning of string * Range.range

(* Objects with metadata *)
type withinfo_t<'a,'t> = {
  v: 'a;
  sort: 't;
  p: Range.range;
}

(* Free term and type variables *)
type var<'t>  = withinfo_t<lident,'t>
type fieldname = lident
(* Term language *)
type sconst = FStar.Const.sconst

type pragma =
  | SetOptions of string
  | ResetOptions

type memo<'a> = ref<option<'a>>

type arg_qualifier =
  | Implicit
  | Equality
type aqual = option<arg_qualifier>
type universe = 
  | U_zero
  | U_succ  of universe
  | U_max   of universe * universe
  | U_bvar  of int
  | U_var   of univ_var
  | U_unif  of Unionfind.uvar<option<universe>>
  | U_unknown
and univ_var = ident

type universe_uvar = Unionfind.uvar<option<universe>>
type univ_vars     = list<univ_var>
type universes     = list<universe>

type term' =
  | Tm_bvar       of bv                //bound variable, referenced by de Bruijn index
  | Tm_name       of bv                //local constant, referenced by a unique name derived from bv.ppname and bv.index
  | Tm_fvar       of fv                //fully qualified reference to a top-level symbol from a module
  | Tm_uinst      of term * universes  //universe instantiation; the first argument must be one of the three constructors above
  | Tm_constant   of sconst 
  | Tm_type       of universe       
  | Tm_abs        of binders * term                              (* fun (xi:ti) -> t *)
  | Tm_arrow      of binders * comp                              (* (xi:ti) -> M t' wp *)
  | Tm_refine     of bv * term                                   (* x:t{phi} *)
  | Tm_app        of term * args                                 (* h tau_1 ... tau_n, args in order from left to right *)
  | Tm_match      of term * list<branch>                         (* match e with b1 ... bn *)
  | Tm_ascribed   of term * term * option<lident>                (* an effect label is the third arg, filled in by the type-checker *)
  | Tm_let        of letbindings * term                          (* let (rec?) x1 = e1 AND ... AND xn = en in e *)
  | Tm_uvar       of uvar * term                                 (* the 2nd arg is the type at which this uvar is introduced *)
  | Tm_delayed    of either<(term * subst_t), unit -> term> 
                   * memo<term>                                  (* A delayed substitution --- always force it; never inspect it directly *)
  | Tm_meta       of term * metadata                             (* Some terms carry metadata, for better code generation, SMT encoding etc. *)
  | Tm_unknown                                                   (* only present initially while desugaring a term *)
and branch = pat * option<term> * term                           (* optional when clause in each branch *)
and pat' =
  | Pat_constant of sconst
  | Pat_disj     of list<pat>                                    (* disjunctive patterns (not allowed to nest): D x | E x -> e *)
  | Pat_cons     of fv * list<(pat * bool)>                      (* flag marks an explicitly provided implicit *)
  | Pat_var      of bv                                           (* a pattern bound variable (linear in a pattern) *)
  | Pat_wild     of bv                                           (* need stable names for even the wild patterns *)
  | Pat_dot_term of bv * term                                    (* dot patterns: determined by other elements in the pattern and type *)
and letbinding = {  //let f : forall u1..un. M t = e 
    lbname :lbname;         //f
    lbunivs:list<univ_var>; //u1..un
    lbtyp  :typ;            //t
    lbeff  :lident;         //M
    lbdef  :term            //e
}
and comp_typ = {
  effect_name:lident;
  result_typ:typ;
  effect_args:args;
  flags:list<cflags>
}
and comp' =
  | Total of typ
  | Comp of comp_typ
and term = syntax<term',term'>
and typ = term                                                   (* sometimes we use typ to emphasize that a term is a type *)
and pat = withinfo_t<pat',term'>
and comp = syntax<comp', unit>
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
  | LEMMA
  | DECREASES of term
and uvar = Unionfind.uvar<uvar_basis<term>>
and metadata =
  | Meta_pattern       of list<args>                             (* Patterns for SMT quantifier instantiation *)
  | Meta_named         of lident                                 (* Useful for pretty printing to keep the type abbreviation around *)
  | Meta_labeled       of string * Range.range * bool            (* Sub-terms in a VC are labeled with error messages to be reported, used in SMT encoding *)
  | Meta_refresh_label of option<bool> * Range.range             (* Add the range to the label of any labeled sub-term of the type *)
  | Meta_desugared     of meta_source_info                       (* Node tagged with some information about source term before desugaring *)
and uvar_basis<'a> =
  | Uvar
  | Fixed of 'a
and meta_source_info =
  | Data_app
  | Sequence
  | Primop                                      (* ... add more cases here as needed for better code generation *)
  | Masked_effect
  | Meta_smt_pat
and fv_qual =
  | Data_ctor
  | Record_projector of lident                  (* the fully qualified (unmangled) name of the field being projected *)
  | Record_ctor of lident * list<fieldname>     (* the type of the record being constructed and its (unmangled) fields in order *)
and lbname = either<bv, lident>
and letbindings = bool * list<letbinding>       (* let recs may have more than one element; top-level lets have lidents *)
and subst_t = list<list<subst_elt>>
and subst_elt = 
   | DB of int * term                          (* DB i t: replace a bound variable with index i with term t *)
   | NM of bv  * int                           (* NM x i: replace a local name with a bound variable i *)
   | NT of bv * term                           (* NT x t: replace a local name with a term t *)
   | UN of univ_var * universe                 (* UN u v: replace universes variable u with universe term v *)
and freenames = set<bv>
and uvars     = set<(uvar*typ)>
and syntax<'a,'b> = {
    n:'a;
    tk:memo<'b>;
    pos:Range.range;
    vars:memo<(freenames * uvars)>;
}
and bv = {
    ppname:ident;  //programmer-provided name for pretty-printing 
    index:int;     //de Bruijn index 0-based, counting up from the binder
    sort:term
}
and fv = var<term> * option<fv_qual>

type tscheme = list<univ_var> * typ

type lcomp = {
    eff_name: lident;
    res_typ: typ;
    cflags: list<cflags>;
    comp: unit -> comp //a lazy computation
}
type freenames_l = list<bv>
type formula = typ
type formulae = list<typ>
val new_bv_set: unit -> set<bv>
val new_uv_set: unit -> uvars

type qualifier =
  | Private
  | Assumption
  | Fresh
  | Opaque
  | Logic
  | Discriminator of lident                          (* discriminator for a datacon l *)
  | Projector of lident * ident                      (* projector for datacon l's argument x *)
  | RecordType of list<fieldname>                    (* unmangled field names *)
  | RecordConstructor of list<fieldname>             (* unmangled field names *)
  | ExceptionConstructor
  | DefaultEffect of option<lident>
  | TotalEffect
  | HasMaskedEffect
  | Effect

type tycon = lident * binders * typ                   (* I (x1:t1) ... (xn:tn) : t *)
type monad_abbrev = {
  mabbrev:lident;
  parms:binders;
  def:typ
  }
type sub_eff = {
  source:lident;
  target:lident;
  lift  :tscheme;
 }

type eff_decl = {
    mname       :lident;
    univs       :univ_vars;
    binders     :binders;
    qualifiers  :list<qualifier>;
    signature   :tscheme;
    ret         :tscheme;
    bind_wp     :tscheme;
    bind_wlp    :tscheme;
    if_then_else:tscheme;
    ite_wp      :tscheme;
    ite_wlp     :tscheme;
    wp_binop    :tscheme;
    wp_as_type  :tscheme;
    close_wp    :tscheme;
    assert_p    :tscheme;
    assume_p    :tscheme;
    null_wp     :tscheme;
    trivial     :tscheme;
}
and sigelt =
  | Sig_tycon          of lident                   //type l forall u1..un. (x1:t1) ... (xn:tn) : t 
                       * univ_vars                 //u1..un
                       * binders                   //(x1:t1) ... (xn:tn)
                       * typ                       //t
                       * list<lident>              //mutually defined types
                       * list<lident>              //data constructors for ths type
                       * list<qualifier>           
                       * Range.range
(* an inductive type is a Sig_bundle of all mutually defined Sig_tycons and Sig_datacons.
   perhaps it would be nicer to let this have a 2-level structure, e.g. list<list<sigelt>>,
   where each higher level list represents one of the inductive types and its constructors.
   However, the current order is convenient as it matches the type-checking order for the mutuals;
   i.e., all the tycons and typ_abbrevs first; then all the data which may refer to the tycons/abbrevs *)
  | Sig_bundle         of list<sigelt>              //the set of mutually defined type and data constructors 
                       * list<qualifier> 
                       * list<lident> 
                       * Range.range
  | Sig_datacon        of lident 
                       * univ_vars                  //universe variables
                       * typ 
                       * lident                     //the inductive type of the value this constructs
                       * list<qualifier> 
                       * list<lident>               //mutually defined types 
                       * Range.range
  | Sig_val_decl       of lident 
                       * univ_vars
                       * typ 
                       * list<qualifier> 
                       * Range.range
  | Sig_let            of letbindings 
                       * Range.range 
                       * list<lident>               //mutually defined
                       * list<qualifier>
  | Sig_main           of term
                       * Range.range
  | Sig_assume         of lident 
                       * formula 
                       * list<qualifier> 
                       * Range.range
  | Sig_new_effect     of eff_decl * Range.range
  | Sig_sub_effect     of sub_eff * Range.range
  | Sig_effect_abbrev  of lident * binders * comp * list<qualifier> * Range.range
  | Sig_pragma         of pragma * Range.range
type sigelts = list<sigelt>

type modul = {
  name: lident;
  declarations: sigelts;
  exports: sigelts;
  is_interface:bool;
}
type path = list<string>
type subst = list<subst_elt>
type mk_t_a<'a,'b> = option<'b> -> range -> syntax<'a, 'b>
type mk_t = mk_t_a<term',term'>

val withsort: 'a -> 'b -> withinfo_t<'a,'b>
val withinfo: 'a -> 'b -> Range.range -> withinfo_t<'a,'b>

(* Constructors for each term form; NO HASH CONSING; just makes all the auxiliary data at each node *)
val mk: 'a -> mk_t_a<'a,'b>

val mk_lb :         (lbname * list<univ_var> * lident * typ * term) -> letbinding
val mk_Tm_app:      term -> args -> mk_t
val extend_app:     term -> arg -> mk_t
val mk_Total:       typ -> comp
val mk_Comp:        comp_typ -> comp
val bv_to_tm:       bv -> term
val bv_to_name:     bv -> term

val bv_eq:           bv -> bv -> Tot<bool>
val order_bv:        bv -> bv -> Tot<int>
val range_of_lbname: lbname -> range
val range_of_bv:     bv -> range

val tun:      term
val teff:     term
val is_teff:  term -> bool
val no_names: freenames
val no_uvs:   uvars

val freenames_of_list:    list<bv> -> freenames
val freenames_of_binders: binders -> freenames
val list_of_freenames:    freenames -> list<bv>
val binders_of_freenames: freenames -> binders
val binders_of_list:      list<bv> -> binders

val null_bv:        term -> bv
val mk_binder:      bv -> binder
val null_binder:    term -> binder
val arg:            term -> arg
val iarg:           term -> arg
val is_null_bv:     bv -> bool
val is_null_binder: binder -> bool
val argpos:         arg -> Range.range
val pat_bvs:        pat -> list<bv>
val is_implicit:    aqual -> bool
val as_implicit:    bool -> aqual

(* gensym *)
val reset_gensym:   (unit -> unit)
val freshen_bv:     bv -> bv
val gen_bv:         string -> option<Range.range> -> typ -> bv 
val new_bv:         option<range> -> typ -> bv
val fv:             lident -> option<fv_qual> -> fv 
val fv_to_tm:       fv -> term
val fvar:           option<fv_qual> -> lident -> range -> term
val fv_eq:          fv -> fv -> bool




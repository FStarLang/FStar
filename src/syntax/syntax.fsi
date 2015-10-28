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

exception Err of string
exception Error of string * Range.range
exception Warning of string * Range.range

type ident = {idText:string;
              idRange:Range.range}
type LongIdent = {ns:list<ident>; //["Microsoft"; "FStar"; "Absyn"; "Syntax"]
                  ident:ident;    //"LongIdent"
                  nsstr:string;
                  str:string}
type lident = LongIdent

(* Objects with metadata *)
type withinfo_t<'a,'t> = {
  v: 'a;
  sort: 't;
  p: Range.range;
}

(* Free term and type variables *)
type var<'t>  = withinfo_t<lident,'t>
type fieldname = lident
type bvdef = {
    ppname:ident; //programmer-provided name for pretty-printing 
    index:int     //de Bruijn index 0-based, counting up from the binder
}
type bvar<'t> = withinfo_t<bvdef,'t>

(* Term language *)
type sconst =
  | Const_unit
  | Const_uint8       of byte
  | Const_bool        of bool
  | Const_int32       of int32
  | Const_int64       of int64
  | Const_int         of string
  | Const_char        of char
  | Const_float       of double
  | Const_bytearray   of array<byte> * Range.range
  | Const_string      of array<byte> * Range.range           (* unicode encoded, F#/Caml independent *)

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
  | U_var   of univ_var
  | U_unif  of Unionfind.uvar<option<universe>>
and univ_var = ident

type universes = list<universe>

type term' =
  | Tm_bvar       of bv * universes  //bound variable, referenced by de Bruijn index
  | Tm_name       of bv * universes  //local constant, referenced by a unique name derived from bv.ppname and bv.index
  | Tm_fvar       of fv * universes  //fully qualified reference to a top-level symbol from a module
  | Tm_constant   of sconst 
  | Tm_type       of universe       
  | Tm_abs        of binders * term                              (* fun (xi:ti) -> t *)
  | Tm_arrow      of binders * comp                              (* (xi:ti) -> M t' wp *)
  | Tm_refine     of bv * term                                   (* x:t{phi} *)
  | Tm_app        of term * args                                 (* h tau_1 ... tau_n, args in order from left to right *)
  | Tm_match      of term * list<(pat * option<term> * term)>    (* optional when clause in each equation *)
  | Tm_ascribed   of term * term * option<lident>                (* an effect label is the third arg, filled in by the type-checker *)
  | Tm_let        of letbindings * term                          (* let (rec?) x1 = e1 AND ... AND xn = en in e *)
  | Tm_uvar       of uvar * term                                 (* the 2nd arg is the type at which this uvar is introduced *)
  | Tm_delayed    of term * subst_t * memo<term>                 (* A delayed substitution --- always force it before inspecting the first arg *)
  | Tm_meta       of meta                                        (* Some terms carry metadata, for better code generation, SMT encoding etc. *)
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
and meta =
  | Meta_pattern       of typ * list<arg>
  | Meta_named         of typ * lident                                 (* Useful for pretty printing to keep the type abbreviation around *)
  | Meta_labeled       of typ * string * Range.range * bool            (* Sub-terms in a VC are labeled with error messages to be reported, used in SMT encoding *)
  | Meta_refresh_label of typ * option<bool> * Range.range             (* Add the range to the label of any labeled sub-term of the type *)
  | Meta_desugared     of term * meta_source_info                       (* Node tagged with some information about source term before desugaring *)
  | Meta_unknown       
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
and lbname = either<bvdef, lident>
and letbindings = bool * list<letbinding>       (* let recs may have more than one element; top-level lets have lidents *)
and subst_t = list<list<subst_elt>>
and subst_elt = bvdef * term
and freevars = set<bv>
and uvars    = set<uvar>
and syntax<'a,'b> = {
    n:'a;
    tk:memo<'b>;
    pos:Range.range;
    fvs:memo<freevars>;
    uvs:memo<uvars>;
}
and bv = bvar<term'>
and fv = var<term'> * option<fv_qual>

type lcomp = {
    eff_name: lident;
    res_typ: typ;
    cflags: list<cflags>;
    comp: unit -> comp //a lazy computation
}
type freevars_l = list<bv>
type formula = typ
type formulae = list<typ>
val new_ftv_set: unit -> set<bv>
val new_uv_set:  unit -> set<Unionfind.uvar<'a>>
val new_uvt_set: unit -> set<(Unionfind.uvar<'a> * 'b)>

type qualifier =
  | Private
  | Assumption
  | Opaque
  | Logic
  | Discriminator of lident                          (* discriminator for a datacon l *)
  | Projector of lident * bvdef                      (* projector for datacon l's argument x *)
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
  lift: typ
 }
type eff_decl = {
    mname:lident;
    binders:binders;
    qualifiers:list<qualifier>;
    signature:typ;
    ret:typ;
    bind_wp:typ;
    bind_wlp:typ;
    if_then_else:typ;
    ite_wp:typ;
    ite_wlp:typ;
    wp_binop:typ;
    wp_as_type:typ;
    close_wp:typ;
    close_wp_t:typ;
    assert_p:typ;
    assume_p:typ;
    null_wp:typ;
    trivial:typ;
}
and sigelt =
  | Sig_tycon          of lident                   //type l (x1:t1) ... (xn:tn) = t 
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
                       * typ 
                       * tycon                      //the inductive type of the value this constructs
                       * list<qualifier> 
                       * list<lident>               //mutually defined types 
                       * Range.range
  | Sig_val_decl       of lident 
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
  is_deserialized:bool
}
type path = list<string>
type subst = list<subst_elt>

val withsort: 'a -> 'b -> withinfo_t<'a,'b>
val withinfo: 'a -> 'b -> Range.range -> withinfo_t<'a,'b>

type mk_t_a<'a,'b> = option<'b> -> range -> syntax<'a, 'b>
type mk_t = mk_t_a<term',term'>
(* Constructors for each term form; NO HASH CONSING; just makes all the auxiliary data at each node *)
val mk: 'a -> mk_t_a<'a,'b>

val mk_lb :         (lbname * list<univ_var> * lident * typ * term) -> letbinding
val mk_Tm_app:     term -> args -> mk_t
//val mk_Tm_app_flat: term -> args -> mk_t
val extend_app:     term -> arg -> mk_t
val mk_Total:       typ -> comp
val mk_Comp:        comp_typ -> comp

val dummyRange:      range
val mk_ident:        (string * range) -> ident
val id_of_text:      string -> ident
val text_of_id:      ident -> string
val text_of_path:    path -> string
val lid_of_ids:      list<ident> -> lident
val ids_of_lid:      lident -> list<ident>
val lid_of_path:     path -> range -> lident
val path_of_lid:     lident -> path
val text_of_lid:     lident -> string
val lid_with_range:  lident -> range -> lident
val range_of_lid:    lident -> range
val lid_equals:      lident -> lident -> Tot<bool>
val bvd_eq:          bvdef -> bvdef -> Tot<bool>
val order_bvd:       bvdef -> bvdef -> Tot<int>
val range_of_lbname: lbname -> range

val tun:     term
val no_fvs:  freevars
val no_uvs:  uvars

val freevars_of_list:    list<bv> -> freevars
val freevars_of_binders: binders -> freevars
val list_of_freevars:    freevars -> list<bv>
val binders_of_freevars: freevars -> binders
val binders_of_list:     list<bv> -> binders

val null_bvar:      term -> bv
val mk_binder:      bv -> binder
val null_binder:    term -> binder
val arg:            term -> arg
val iarg:           term -> arg
val is_null_pp:     bvdef -> bool
val is_null_bvd:    bvdef -> bool
val is_null_bvar:   bv -> bool
val is_null_binder: binder -> bool
val argpos:         arg -> Range.range
val pat_vars:       pat -> list<bvdef>
val is_implicit:    aqual -> bool
val as_implicit:    bool -> aqual






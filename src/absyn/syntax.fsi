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
module FStar.Absyn.Syntax
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
(* Bound variables. 'a is a phantom type to distinguish between term and
   type bound variables. 't is the type or the kind of the variable. *)
type bvdef<'a> = {ppname:ident; realname:ident}
type bvar<'a,'t> = withinfo_t<bvdef<'a>,'t>
(* Bound vars have a name for pretty printing,
   and a unique name generated during desugaring.
   Only the latter is used during type checking.  *)

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
type typ' =
  | Typ_btvar    of btvar
  | Typ_const    of ftvar
  | Typ_fun      of binders * comp                           (* (ai:ki|xi:ti) -> M t' wp *)
  | Typ_refine   of bvvar * typ                              (* x:t{phi} *)
  | Typ_app      of typ * args                               (* args in order *)
  | Typ_lam      of binders * typ                            (* fun (ai|xi:tau_i) => T *)
  | Typ_ascribed of typ * knd                                (* t <: k *)
  | Typ_meta     of meta_t                                   (* Not really in the type language; a way to stash convenient metadata with types *)
  | Typ_uvar     of uvar_t * knd                             (* Unification variables, not present after 1st round tc *)
  | Typ_delayed  of either<(typ * subst_t), (unit -> typ)> * memo<typ>                  (* A delayed substitution---always force it before inspecting the first arg *)
  | Typ_unknown                                              (* not present after 1st round tc *)
and arg = either<typ,exp> * aqual                            (* marks an explicitly provided implicit arg *)
and args = list<arg>
and binder = either<btvar,bvvar> * aqual                     (* f:   #n:nat -> vector n int -> T; f #17 v *)
and binders = list<binder>                                   (* bool marks implicit binder *)
and typ = syntax<typ',knd>                                   (* A type is a typ' + its kind as metadata *)
and comp_typ = {
  effect_name:lident;
  result_typ:typ;
  effect_args:args;
  flags:list<cflags>
  }
and comp' =
  | Total of typ
  | Comp of comp_typ
and comp = syntax<comp', unit>
and cflags =
  | TOTAL
  | MLEFFECT
  | RETURN
  | PARTIAL_RETURN
  | SOMETRIVIAL
  | LEMMA
  | DECREASES of exp
and uvar_t = Unionfind.uvar<uvar_basis<typ>>
and meta_t =
  | Meta_pattern       of typ * list<arg>
  | Meta_named         of typ * lident                                 (* Useful for pretty printing to keep the type abbreviation around *)
  | Meta_labeled       of typ * string * Range.range * bool            (* Sub-terms in a VC are labeled with error messages to be reported, used in SMT encoding *)
  | Meta_refresh_label of typ * option<bool> * Range.range             (* Add the range to the label of any labeled sub-term of the type *)
  | Meta_slack_formula of typ * typ * ref<bool>                        (* A refinement formula with slack, used in type inference; boolean marks if the slack is gone *)
and uvar_basis<'a> =
  | Uvar
  | Fixed of 'a
and exp' =
  | Exp_bvar       of bvvar
  | Exp_fvar       of fvvar * option<fv_qual>
  | Exp_constant   of sconst
  | Exp_abs        of binders * exp
  | Exp_app        of exp * args                                 (* h tau_1 ... tau_n, args in order from left to right *)
  | Exp_match      of exp * list<(pat * option<exp> * exp)>      (* optional when clause in each equation *)
  | Exp_ascribed   of exp * typ * option<lident>
  | Exp_let        of letbindings * exp                          (* let (rec?) x1 = e1 AND ... AND xn = en in e *)
  | Exp_uvar       of uvar_e * typ                               (* not present after 1st round tc *)
  | Exp_delayed    of exp * subst_t * memo<exp>                    (* A delayed substitution --- always force it before inspecting the first arg *)
  | Exp_meta       of meta_e                                     (* No longer tag every expression with info, only selectively *)
and exp = syntax<exp',typ>
and meta_e =
  | Meta_desugared     of exp * meta_source_info                 (* Node tagged with some information about source term before desugaring *)
and meta_source_info =
  | Data_app
  | Sequence
  | Primop                                  (* ... add more cases here as needed for better code generation *)
  | Masked_effect
  | Meta_smt_pat
and fv_qual =
  | Data_ctor
  | Record_projector of lident                  (* the fully qualified (unmangled) name of the field being projected *)
  | Record_ctor of lident * list<fieldname>     (* the type of the record being constructed and its (unmangled) fields in order *)
and uvar_e = Unionfind.uvar<uvar_basis<exp>>
and btvdef = bvdef<typ>
and bvvdef = bvdef<exp>
and pat' =
  | Pat_disj     of list<pat>
  | Pat_constant of sconst
  | Pat_cons     of fvvar * option<fv_qual> * list<(pat * bool)>  (* flag marks an explicitly provided implicit *)
  | Pat_var      of bvvar
  | Pat_tvar     of btvar
  | Pat_wild     of bvvar                                         (* need stable names for even the wild patterns *)
  | Pat_twild    of btvar
  | Pat_dot_term of bvvar * exp
  | Pat_dot_typ  of btvar * typ
and pat = withinfo_t<pat',option<either<knd,typ>>>                (* the meta-data is a typ, except for Pat_dot_typ and Pat_tvar, where it is a kind (not strictly needed) *)
and knd' =
  | Kind_type                                             (*Type*)
  | Kind_effect
  | Kind_abbrev of kabbrev * knd                          (* keep the abbreviation around for printing *)
  | Kind_arrow of binders * knd                           (* (ai:ki|xi:ti) => k' *) (*are they really in order, e.g. all kind args first and then the type args?*)
  | Kind_uvar of uvar_k_app                               (* not present after 1st round tc *)
  | Kind_lam of binders * knd                             (* not present after 1st round tc *)
  | Kind_delayed of knd * subst_t * memo<knd>             (* delayed substitution --- always force before inspecting first element *)
  | Kind_unknown                                          (* not present after 1st round tc *)
and knd = syntax<knd', unit>
and uvar_k_app = uvar_k * args
and kabbrev = lident * args
and uvar_k = Unionfind.uvar<uvar_basis<knd>>
and lbname = either<bvvdef, lident>
and letbinding = {
    lbname:lbname;
    lbtyp:typ;
    lbeff:lident;
    lbdef:exp
}
and letbindings = bool * list<letbinding> (* let recs may have more than one element; top-level lets have lidents *)
and subst_t = list<list<subst_elt>>
//and subst_map = Util.smap<either<typ, exp>>
and subst_elt = either<(btvdef*typ), (bvvdef*exp)>
and fvar = either<btvdef, bvvdef>
and freevars = {
  ftvs: set<btvar>;
  fxvs: set<bvvar>;
}
and uvars = {
  uvars_k: set<uvar_k>;
  uvars_t: set<(uvar_t*knd)>;
  uvars_e: set<(uvar_e*typ)>;
}
and syntax<'a,'b> = {
    n:'a;
    tk:memo<'b>;
    pos:Range.range;
    fvs:memo<freevars>;
    uvs:memo<uvars>;
}
and btvar = bvar<typ,knd>
and bvvar = bvar<exp,typ>
and ftvar = var<knd>
and fvvar = var<typ>

type ktec =
    | K of knd
    | T of typ * option<knd>
    | E of exp
    | C of comp

type lcomp = {
    eff_name: lident;
    res_typ: typ;
    cflags: list<cflags>;
    comp: unit -> comp //a lazy computation
    }
type either_var = either<btvar, bvvar>
type freevars_l = list<either_var>
type formula = typ
type formulae = list<typ>
val new_ftv_set: unit -> set<bvar<'a,'b>>
val new_uv_set: unit -> set<Unionfind.uvar<'a>>
val new_uvt_set: unit -> set<(Unionfind.uvar<'a> * 'b)>

type qualifier =
  | Private
  | Assumption
  | Opaque
  | Logic
  | Discriminator of lident                          (* discriminator for a datacon l *)
  | Projector of lident * either<btvdef, bvvdef>     (* projector for datacon l's argument 'a or x *)
  | RecordType of list<fieldname>                    (* unmangled field names *)
  | RecordConstructor of list<fieldname>             (* unmangled field names *)
  | ExceptionConstructor
  | DefaultEffect of option<lident>
  | TotalEffect
  | HasMaskedEffect
  | Effect

type tycon = lident * binders * knd
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
    signature:knd;
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
  | Sig_tycon          of lident * binders * knd * list<lident> * list<lident> * list<qualifier> * Range.range
  (* list<lident> identifies mutuals, second list<lident> are all the constructors *)
  | Sig_kind_abbrev    of lident * binders * knd * Range.range
  | Sig_typ_abbrev     of lident * binders * knd * typ * list<qualifier> * Range.range
  | Sig_datacon        of lident * typ * tycon * list<qualifier> * list<lident> (* mutuals *) * Range.range
  (* the tycon is the inductive type of the value this constructs *)
  | Sig_val_decl       of lident * typ * list<qualifier> * Range.range
  | Sig_assume         of lident * formula * list<qualifier> * Range.range
  | Sig_let            of letbindings * Range.range * list<lident> * list<qualifier>
  | Sig_main           of exp * Range.range
  | Sig_bundle         of list<sigelt> * list<qualifier> * list<lident> * Range.range
    (* an inductive type is a bundle of all mutually defined Sig_tycons and Sig_datacons *)
    (* perhaps it would be nicer to let this have a 2-level structure, e.g. list<list<sigelt>>,
       where each higher level list represents one of the inductive types and its constructors.
       NS: the current order is convenient as it matches the type-checking order for the mutuals;
           all the tycons and typ_abbrevs first; then all the data which may refer to the tycons/abbrevs *)
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
val syn: 'a -> 'b -> ('b -> 'a -> 'c) -> 'c
val dummyRange: range
val mk_ident: (string * range) -> ident
val id_of_text: string -> ident
val text_of_id: ident -> string
val text_of_path: path -> string
val lid_equals: lident -> lident -> Tot<bool>
val bvd_eq: bvdef<'a> -> bvdef<'a> -> Tot<bool>
val order_bvd: either<bvdef<'a>, bvdef<'b>> -> either<bvdef<'c>, bvdef<'d>> -> int
val lid_with_range: lident -> range -> lident
val range_of_lid: lident -> range
val range_of_lbname: lbname -> range
val lid_of_ids: list<ident> -> lident
val ids_of_lid: lident -> list<ident>
val lid_of_path: path -> range -> lident
val path_of_lid: lident -> path
val text_of_lid: lident -> string
val withsort: 'a -> 'b -> withinfo_t<'a,'b>
val withinfo: 'a -> 'b -> Range.range -> withinfo_t<'a,'b>

val ktype:knd
val keffect: knd
val kun:knd
val tun:typ
val no_fvs: freevars
val no_uvs: uvars
val freevars_of_list: list<either<btvar, bvvar>> -> freevars
val freevars_of_binders: binders -> freevars
val list_of_freevars: freevars -> list<either<btvar,bvvar>>
val binders_of_freevars: freevars -> binders
val binders_of_list: list<either<btvar, bvvar>> -> binders

val mk_Kind_unknown: knd
val mk_Kind_type: knd
val mk_Kind_effect:knd
val mk_Kind_abbrev: (kabbrev * knd) -> range -> knd
val mk_Kind_arrow: (binders * knd) -> range -> knd
val mk_Kind_arrow': (binders * knd) -> range -> knd
val mk_Kind_delayed: (knd * subst_t * memo<knd>) -> range -> knd
val mk_Kind_uvar: uvar_k_app -> range -> knd
val mk_Kind_lam: (binders * knd) -> range -> knd

val mk_Typ_unknown: typ
val mk_Typ_btvar: btvar -> option<knd> -> range -> typ
val mk_Typ_const: ftvar -> option<knd> -> range -> typ
val mk_Typ_fun: (binders * comp) -> option<knd> -> range -> typ
//val mk_Typ_fun': (binders * comp) -> option<knd> -> range -> typ
val mk_Typ_refine: (bvvar * formula) -> option<knd> -> range -> typ
val mk_Typ_app: (typ * args) -> option<knd> -> range -> typ
val mk_Typ_app': (typ * args) -> option<knd> -> range -> typ
val mk_Typ_lam: (binders * typ) -> option<knd> -> range -> typ
val mk_Typ_lam': (binders * typ) -> option<knd> -> range -> typ
val mk_Typ_ascribed': (typ * knd) -> option<knd> -> range -> typ
val mk_Typ_ascribed: (typ * knd) -> range -> typ
val mk_Typ_meta': meta_t -> option<knd> -> range -> typ
val mk_Typ_meta: meta_t -> typ
val mk_Typ_uvar': (uvar_t * knd) -> option<knd> -> range -> typ
val mk_Typ_uvar: (uvar_t * knd) -> range -> typ
val mk_Typ_delayed: (typ * subst_t * memo<typ>) -> option<knd> -> range -> typ
val mk_Typ_delayed': either<(typ * subst_t), (unit -> typ)> -> option<knd> -> range -> typ

val extend_typ_app: (typ * arg) -> option<knd> -> range -> typ

val mk_Total: typ -> comp
val mk_Comp: comp_typ -> comp

val mk_Exp_bvar: bvvar -> option<typ> -> range -> exp
val mk_Exp_fvar: (fvvar * option<fv_qual>) -> option<typ> -> range -> exp
val mk_Exp_constant: sconst -> option<typ> -> range -> exp
val mk_Exp_abs: (binders * exp) -> option<typ> -> range -> exp
val mk_Exp_abs': (binders * exp) -> option<typ> -> range -> exp
val mk_Exp_app: (exp * args) -> option<typ> -> range -> exp
val mk_Exp_app': (exp * args) -> option<typ> -> range -> exp
val mk_Exp_app_flat: (exp * args) -> option<typ> -> range -> exp
val mk_Exp_match: (exp * list<(pat * option<exp> * exp)>) -> option<typ> -> range -> exp
val mk_Exp_ascribed: (exp * typ * option<lident>) -> option<typ> -> range -> exp
val mk_Exp_let: (letbindings * exp) -> option<typ> -> range -> exp
val mk_Exp_uvar': (uvar_e * typ) -> option<typ> -> range -> exp
val mk_Exp_uvar: (uvar_e * typ) -> range -> exp
val mk_Exp_delayed: (exp * subst_t * memo<exp>) -> option<typ> -> range -> exp
val mk_Exp_meta' : meta_e -> option<typ> -> range -> exp
val mk_Exp_meta: meta_e -> exp
val mk_lb : (lbname * lident * typ * exp) -> letbinding

//val mk_subst: subst -> subst
//val extend_subst: subst_elt -> subst -> subst

val null_bvar: 'b -> bvar<'a,'b>
val t_binder: btvar -> binder
val v_binder: bvvar -> binder
val null_t_binder: knd -> binder
val null_v_binder: typ -> binder
val targ: typ -> arg
val varg: exp -> arg
val itarg: typ -> arg
val ivarg: exp -> arg
val is_null_pp: bvdef<'a> -> bool
val is_null_bvd: bvdef<'a> -> bool
val is_null_bvar: bvar<'a,'b> -> bool
val is_null_binder: binder -> bool
val argpos: arg -> Range.range
val pat_vars: pat -> list<either<btvdef,bvvdef>>
val is_implicit: aqual -> bool
val as_implicit: bool -> aqual






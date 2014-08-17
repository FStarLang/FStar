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
module Microsoft.FStar.Absyn.Syntax
(* Type definitions for the core AST *)

open Prims
open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.LazySet
open Microsoft.FStar.Range

exception Err of string
exception Error of string * Range.range
exception Warning of string * Range.range
 
type ident = {idText:string;
              idRange:Range.range}
type LongIdent = {ns:list<ident>; 
                  ident:ident; 
                  nsstr:string;
                  str:string}
type lident = LongIdent
type withinfo_t<'a,'t> = {
  v: 'a; 
  sort: 't;
  p: Range.range; 
} 
type var<'t>  = withinfo_t<lident,'t>
type fieldname = lident
type inst<'a> = ref<option<'a>>
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
  | Const_char        of char
  | Const_float       of double
  | Const_bytearray   of array<byte> * Range.range 
  | Const_string      of array<byte> * Range.range           (* unicode encoded, F#/Caml independent *)

type memo<'a> = ref<option<'a>>
type typ' =  
  | Typ_btvar    of btvar
  | Typ_const    of ftvar 
  | Typ_fun      of option<bvvdef> * typ * comp * bool       (* x:t -> M t' wp  or  t -> M t' wp, bool marks implicit arguments *)
  | Typ_univ     of btvdef * knd  * comp                     (* 'a:k -> M t wp *)
  | Typ_refine   of bvvdef * typ * typ                       (* x:t{phi} *)
  | Typ_app      of typ * typ * bool                         (* t t' -- bool marks an explicitly provided implicit arg *) 
  | Typ_dep      of typ * exp * bool                         (* t e -- bool marks an explicitly provided implicit arg *)  
  | Typ_lam      of bvvdef * typ * typ                       (* fun (x:t) => T *)
  | Typ_tlam     of btvdef * knd * typ                       (* fun ('a:k) => T *) 
  | Typ_ascribed of typ * knd                                (* t <: k *)
  | Typ_meta     of meta_t                                   (* Not really in the type language; a way to stash convenient metadata with types *)
  | Typ_uvar     of uvar_t * knd                             (* not present after 1st round tc *)
  | Typ_delayed  of typ * subst * memo<typ>                  (* A delayed substitution---always force it before inspecting the first arg *)
  | Typ_unknown                                              (* not present after 1st round tc *)
and typ = syntax<typ',knd>
and comp_typ = {
  effect_name:lident; 
  result_typ:typ; 
  effect_args:list<either<typ,exp>>;
  flags:list<cflags>
  }
and comp' = 
  | Total of typ
  | Comp of comp_typ                    
  | Flex of uvar_c * typ
and comp = syntax<comp', unit>
and cflags = 
  | TOTAL 
  | MLEFFECT 
  | RETURN 
  | SOMETRIVIAL
and uvar_c = Unionfind.uvar<comp_typ_uvar_basis>
and comp_typ_uvar_basis = 
  | Floating 
  | Resolved of comp
and uvar_t = Unionfind.uvar<uvar_basis<typ,knd>>
and meta_t = 
  | Meta_pattern of typ * list<either<typ,exp>>
  | Meta_named of typ * lident                               (* Useful for pretty printing to keep the type abbreviation around *)
and uvar_basis<'a,'b> = 
  | Uvar of ('a -> 'b -> bool)                               (* A well-formedness check to ensure that all names are in scope *)
  | Fixed of 'a
and exp' =
  | Exp_bvar       of bvvar
  | Exp_fvar       of fvvar * bool                            (* flag indicates a constructor *)
  | Exp_constant   of sconst
  | Exp_abs        of bvvdef * typ * exp 
  | Exp_tabs       of btvdef * knd * exp            
  | Exp_app        of exp * exp * bool                           (* flag indicates whether the argument is explicit instantiation of an implict param *)
  | Exp_tapp       of exp * typ             
  | Exp_match      of exp * list<(pat * option<exp> * exp)>      (* optional when clause in each equation *)
  | Exp_ascribed   of exp * typ 
  | Exp_let        of letbindings * exp                          (* let (rec?) x1 = e1 AND ... AND xn = en in e *)
  | Exp_uvar       of uvar_e * typ                               (* not present after 1st round tc *)
  | Exp_delayed    of exp * subst * memo<exp>                    (* A delayed substitution --- always force it before inspecting the first arg *)
  | Exp_meta       of meta_e                                     (* No longer tag every expression with info, only selectively *)
and exp = syntax<exp',typ>
and meta_e = 
  | Meta_desugared of exp * meta_source_info                     (* Node tagged with some information about source term before desugaring *)
  | Meta_datainst  of exp * option<typ>                          (* Expect the data constructor e to build a t-typed value; only used internally to pretyping; not visible elsewhere *)
and meta_source_info =
  | Data_app
  | Sequence                   
  | Primop                                  (* ... add more cases here as needed for better code generation *)
and uvar_e = Unionfind.uvar<uvar_basis<exp,typ>>
and btvdef = bvdef<typ>
and bvvdef = bvdef<exp>
and pat = 
  | Pat_cons     of lident * list<pat>
  | Pat_var      of bvvdef
  | Pat_tvar     of btvdef
  | Pat_constant of sconst
  | Pat_disj     of list<pat>
  | Pat_wild
  | Pat_twild
  | Pat_withinfo of pat * Range.range
and knd' =
  | Kind_type
  | Kind_effect
  | Kind_abbrev of kabbrev * knd                          (* keep the abbreviation around for printing *)
  | Kind_tcon of option<btvdef> * knd * knd * bool    (* 'a:k -> k'; bool marks implicit *)
  | Kind_dcon of option<bvvdef> * typ * knd * bool        (* x:t -> k; bool marks implicit *)
  | Kind_uvar of uvar_k                                   (* not present after 1st round tc *)
  | Kind_delayed of knd * subst * memo<knd>               (* delayed substitution --- always force before inspecting first element *)
  | Kind_unknown                                          (* not present after 1st round tc *)
and knd = syntax<knd', unit>

and kabbrev = lident * list<either<typ,exp>>
and uvar_k = Unionfind.uvar<uvar_basis<knd,unit>>
and lbname = either<bvvdef, lident>
and letbindings = bool * list<(lbname * typ * exp)> (* let recs may have more than one element; top-level lets have lidents *)
and subst' = list<subst_elt>
and subst = {
    subst:subst';
    subst_fvs:memo<freevars>;
}
and subst_map = Util.smap<either<typ, exp>>
and subst_elt = either<(btvdef*typ), (bvvdef*exp)>
and fvar = either<btvdef, bvvdef>
and freevars = {
  ftvs: list<btvar>;
  fxvs: list<bvvar>;
}
and uvars = {
  uvars_k: list<uvar_k>;
  uvars_t: list<(uvar_t*knd)>;
  uvars_e: list<(uvar_e*typ)>;
  uvars_c: list<uvar_c>;
}
and syntax<'a,'b> = {
    n:'a;
    tk:'b;
    pos:Range.range;
    fvs:memo<freevars>;
    uvs:memo<uvars>;
}
and btvar = bvar<typ,knd>
and bvvar = bvar<exp,typ>
and ftvar = var<knd>
and fvvar = var<typ>

type formula = typ
type formulae = list<typ>

type tparam =
  | Tparam_typ  of btvdef * knd (* idents for pretty printing *)
  | Tparam_term of bvvdef * typ

type qualifier = 
  | Private 
  | Public 
  | Assumption
  | Definition  
  | Query
  | Lemma
  | Logic
  | Discriminator of lident                          (* discriminator for a datacon l *)
  | Projector of lident * either<btvdef, bvvdef>     (* projector for datacon l's argument 'a or x *)
  | RecordType of list<ident>                        (* unmangled field names *)
  | RecordConstructor of list<ident>                 (* unmangled field names *)
  | ExceptionConstructor
  | Effect 
 
type monad_abbrev = {
  mabbrev:lident;
  parms:list<tparam>;
  def:typ
  }
type monad_order = {
  source:lident;
  target:lident;
  lift: typ
 }
type monad_lat = list<monad_order>
type monad_decl = {
    mname:lident;
    total:bool;
    signature:knd;
    ret:typ;
    bind_wp:typ;
    bind_wlp:typ;
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
    abbrevs:list<sigelt> 
 }
and sigelt =
  | Sig_tycon          of lident * list<tparam> * knd * list<lident> * list<lident> * list<qualifier> * Range.range (* bool is for a prop, list<lident> identifies mutuals, second list<lident> are all the constructors *)
  | Sig_typ_abbrev     of lident * list<tparam> * knd * typ * list<qualifier> * Range.range 
  | Sig_datacon        of lident * typ * lident * list<qualifier> * Range.range  (* second lident is the name of the type this constructs *)
  | Sig_val_decl       of lident * typ * list<qualifier> * Range.range 
  | Sig_assume         of lident * formula * list<qualifier> * Range.range 
  | Sig_let            of letbindings * Range.range 
  | Sig_main           of exp * Range.range 
  | Sig_bundle         of list<sigelt> * Range.range  (* an inductive type is a bundle of all mutually defined Sig_tycons and Sig_datacons *)
  | Sig_monads         of list<monad_decl> * monad_lat * Range.range
type sigelts = list<sigelt>

type modul = {
  name: lident;
  declarations: sigelts;
  exports: sigelts;
  is_interface:bool
}
type path = list<string>

val syn: 'a -> 'b -> ('b -> 'a -> 'c) -> 'c
val dummyRange: range
val mk_ident: (string * range) -> ident
val id_of_text: string -> ident
val text_of_id: ident -> string
val text_of_path: path -> string
val lid_equals: lident -> lident -> Tot<bool>
val bvd_eq: bvdef<'a> -> bvdef<'a> -> Tot<bool>
val order_bvd: either<bvdef<'a>, bvdef<'b>> -> either<bvdef<'c>, bvdef<'d>> -> int
val range_of_lid: lident -> range
val range_of_lbname: lbname -> range
val lid_of_ids: list<ident> -> lident
val ids_of_lid: lident -> list<ident>
val lid_of_path: path -> range -> lident
val path_of_lid: lident -> path
val text_of_lid: lident -> string
val withsort: 'a -> 'b -> withinfo_t<'a,'b>

val ktype:knd
val kun:knd
val tun:typ
val no_fvs: freevars
val no_uvs: uvars

val mk_Kind_type: knd
val mk_Kind_effect:knd
val mk_Kind_abbrev: (kabbrev * knd) -> range -> knd
val mk_Kind_tcon: (option<btvdef> * knd * knd * bool) -> range -> knd
val mk_Kind_dcon: (option<bvvdef> * typ * knd * bool) -> range -> knd
val mk_Kind_delayed: (knd * subst * memo<knd>) -> range -> knd
val mk_Kind_uvar: uvar_k -> range -> knd

val mk_Typ_btvar: btvar -> knd -> range -> typ
val mk_Typ_const: ftvar -> knd -> range -> typ
val mk_Typ_fun: (option<bvvdef> * typ * comp * bool) -> knd -> range -> typ
val mk_Typ_univ: (btvdef * knd * comp) -> knd -> range -> typ
val mk_Typ_refine: (bvvdef * typ * formula) -> knd -> range -> typ
val mk_Typ_app: (typ * typ * bool) -> knd -> range -> typ
val mk_Typ_dep: (typ * exp * bool) -> knd -> range -> typ
val mk_Typ_lam: (bvvdef * typ * typ) -> knd -> range -> typ
val mk_Typ_tlam: (btvdef * knd * typ) -> knd -> range -> typ
val mk_Typ_ascribed': (typ * knd) -> knd -> range -> typ
val mk_Typ_ascribed: (typ * knd) -> range -> typ
val mk_Typ_meta': meta_t -> knd -> range -> typ
val mk_Typ_meta: meta_t -> typ
val mk_Typ_uvar': (uvar_t * knd) -> knd -> range -> typ
val mk_Typ_uvar: (uvar_t * knd) -> range -> typ
val mk_Typ_delayed: (typ * subst * memo<typ>) -> knd -> range -> typ

val mk_Total: typ -> comp
val mk_Comp: comp_typ -> comp
val mk_Flex: (uvar_c * typ) -> comp

val mk_Exp_bvar: bvvar -> typ -> range -> exp
val mk_Exp_fvar: (fvvar * bool) -> typ -> range -> exp 
val mk_Exp_constant: sconst -> typ -> range -> exp
val mk_Exp_abs: (bvvdef * typ * exp) -> typ -> range -> exp
val mk_Exp_tabs: (btvdef * knd * exp) -> typ -> range -> exp
val mk_Exp_app: (exp * exp * bool) -> typ -> range -> exp
val mk_Exp_tapp: (exp * typ) -> typ -> range -> exp
val mk_Exp_match: (exp * list<(pat * option<exp> * exp)>) -> typ -> range -> exp
val mk_Exp_ascribed': (exp * typ) -> typ -> range -> exp
val mk_Exp_ascribed: (exp * typ) -> range -> exp
val mk_Exp_let: (letbindings * exp) -> typ -> range -> exp
val mk_Exp_uvar': (uvar_e * typ) -> typ -> range -> exp
val mk_Exp_uvar: (uvar_e * typ) -> range -> exp
val mk_Exp_delayed: (exp * subst * memo<exp>) -> typ -> range -> exp
val mk_Exp_meta' : meta_e -> typ -> range -> exp
val mk_Exp_meta: meta_e -> exp

val mk_subst: subst' -> subst
val extend_subst: subst_elt -> subst -> subst





val pat_vars: range -> pat -> list<either<btvdef,bvvdef>>






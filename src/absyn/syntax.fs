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

open Microsoft.FStar
open Microsoft.FStar.Util

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
type bvdef<'a> = {ppname:ident; realname:ident; instantiation:inst<'a>}
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
  | Const_bytearray   of byte[] * Range.range 
  | Const_string      of byte[] * Range.range (* unicode encoded, F#/Caml independent *)

type typ =  
  | Typ_btvar    of bvar<typ,kind>
  | Typ_const    of var<kind> 
  | Typ_fun      of option<bvvdef> * typ * typ * bool   (* x:t -> t'  or  t -> t', bool is a flag marking implicit arguments *)
  | Typ_univ     of btvdef * kind  * typ                (* 'a:k -> t *)
  | Typ_refine   of bvvdef * typ * typ                  (* x:t{phi} *)
  | Typ_app      of typ * typ * bool                    (* t t' -- bool marks an explicitly provided implicit arg *) 
  | Typ_dep      of typ * exp * bool                    (* t e -- bool marks an explicitly provided implicit arg *)  
  | Typ_lam      of bvvdef * typ * typ                  (* fun (x:t) => T *)
  | Typ_tlam     of btvdef * kind * typ                 (* fun ('a:k) => T *) 
  | Typ_ascribed of typ * kind                          (* t <: k *)
  | Typ_meta     of meta_t                              (* Not really in the type language; a way to stash convenient metadata with types *)
  | Typ_uvar     of uvar_t * kind                       (* not present after 1st round tc *)
  | Typ_unknown                                         (* not present after 1st round tc *)
and uvar_t = Unionfind.uvar<uvar_basis<typ,kind>>
and meta_t = 
  | Meta_pos of typ * Range.range                       (* user wrote down this type 1 at source position 2 *)
  | Meta_pattern of typ * list<either<typ,exp>>
  | Meta_cases of list<typ>
  | Meta_tid of int
and uvar_basis<'a,'b> = 
  | Uvar of ('a -> 'b -> bool)                          (* A well-formedness check to ensure that all names are in scope *)
  | Fixed of 'a
and exp =
  | Exp_bvar       of bvar<exp,typ>
  | Exp_fvar       of var<typ> * bool                            (* flag indicates a constructor *)
  | Exp_constant   of sconst
  | Exp_abs        of bvvdef * typ * exp 
  | Exp_tabs       of btvdef * kind * exp            
  | Exp_app        of exp * exp * bool                           (* flag indicates whether the argument is explicit instantiation of an implict param *)
  | Exp_tapp       of exp * typ             
  | Exp_match      of exp * list<(pat * option<exp> * exp)>      (* optional when clause in each equation *)
  | Exp_ascribed   of exp * typ 
  | Exp_let        of letbindings * exp                          (* let (rec?) x1 = e1 AND ... AND xn = en in e *)
  | Exp_primop     of ident * list<exp>
  | Exp_uvar       of uvar_e * typ                               (* not present after 1st round tc *)
  | Exp_meta       of meta_e                                     (* No longer tag every expression with info, only selectively *)
and meta_e = 
  | Meta_info      of exp * typ * Range.range                    (* Expression tagged with typ and position info *)
  | Meta_desugared of exp * meta_source_info                     (* Node tagged with some information about source term before desugaring *)
  | Meta_datainst  of exp * typ                                  (* Expect the data constructor e to build a t-typed value; only used internally to pretyping; not visible elsewhere *)
and meta_source_info =
  | Data_app
  | Sequence                                                     (* ... add more cases here as needed for better code generation *)
and uvar_e = Unionfind.uvar<uvar_basis<exp,typ>>
and btvdef = bvdef<typ>
and bvvdef = bvdef<exp>
and pat = 
  | Pat_cons     of lident * list<pat>
  | Pat_var      of bvvdef
  | Pat_tvar     of bvdef<typ>
  | Pat_constant of sconst
  | Pat_disj     of list<pat>
  | Pat_wild
  | Pat_twild
  | Pat_withinfo of pat * Range.range
and kind =
  | Kind_star
  | Kind_tcon of option<bvdef<typ>> * kind * kind * bool  (* 'a:k -> k'; bool marks implicit *)
  | Kind_dcon of option<bvvdef> * typ * kind * bool       (* x:t -> k; bool marks implicit *)
  | Kind_uvar of uvar_k                                   (* not present after 1st round tc *)
  | Kind_unknown                                          (* not present after 1st round tc *)
and uvar_k = Unionfind.uvar<uvar_basis<kind,unit>>
and letbindings = bool * list<(either<bvvdef,lident> * typ * exp)> (* let recs may have more than one element; top-level lets have lidents *)

type formula = typ
type btvar = bvar<typ,kind>
type bvvar = bvar<exp,typ>

type tparam =
  | Tparam_typ  of btvdef * kind (* idents for pretty printing *)
  | Tparam_term of bvvdef * typ

type aqual = 
  | Private 
  | Public

type logic_array = {array_sel:LongIdent;
                    array_upd:LongIdent;
                    array_emp:LongIdent;
                    array_indom:LongIdent}
type logic_tag =
  | Logic_data 
  | Logic_tfun
  | Logic_array of logic_array
  | Logic_discriminator
  | Logic_projector
  | Logic_record
  | Logic_val
  | Logic_type

type atag = 
  | Assumption
  | Definition
  | Lemma

type sigelt =
  | Sig_tycon          of lident * list<tparam> * kind * list<lident> * list<lident> * list<logic_tag> (* bool is for a prop, list<lident> identifies mutuals, second list<lident> are all the constructors *)
  | Sig_typ_abbrev     of lident * list<tparam> * kind * typ
  | Sig_datacon        of lident * typ * lident (* second lident is the name of the type this constructs *)
  | Sig_val_decl       of lident * typ * option<atag> * option<logic_tag>
  | Sig_assume         of lident * formula * aqual * atag
  | Sig_logic_function of lident * typ * list<logic_tag>
  | Sig_let            of letbindings
  | Sig_main           of exp
  | Sig_bundle         of list<sigelt>  (* an inductive type is a bundle of all mutually defined Sig_tycons and Sig_datacons *)
type sigelts = list<sigelt>

type modul = {
  name: lident;
  declarations: sigelts;
  exports: sigelts;
}

(*********************************************************************************)
(* Identifiers to/from strings *)    
(*********************************************************************************)
type path = list<string>
let dummyRange = 0L
let mk_ident (text,range) = {idText=text; idRange=range}
let id_of_text str = mk_ident(str, dummyRange)
let text_of_id (id:ident) = id.idText
let text_of_path path = Util.concat_l "." path
let path_of_text text = String.split ['.'] text 
let path_of_lid lid = List.map text_of_id (lid.ns@[lid.ident])
let ids_of_lid lid = lid.ns@[lid.ident]
let lid_of_ids ids = 
    let ns, id = Util.prefix ids in 
    let nsstr = List.map text_of_id ns |> text_of_path in
    {ns=ns; 
     ident=id; 
     nsstr=nsstr; 
     str=(if nsstr="" then id.idText else nsstr ^ "." ^ id.idText)}
let lid_of_path path pos = 
    let ids = List.map (fun s -> mk_ident(s, pos)) path in
    lid_of_ids ids
let text_of_lid lid = lid.str
let lid_equals l1 l2 = l1.str = l2.str

let withinfo v s r = {v=v; sort=s; p=r}
let withsort v s = withinfo v s dummyRange
let ewithpos v r = {v=v; sort=Typ_unknown; p=r}

let range_of_lid (lid:LongIdent) = lid.ident.idRange

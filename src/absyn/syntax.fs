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
type LongIdent = {lid:ident list; str:string}
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
  | Typ_fun      of option<bvvdef> * typ * typ          (* x:t -> t'  or  t -> t' *)
  | Typ_univ     of btvdef * kind  * typ                (* 'a:k -> t *)
  | Typ_refine   of bvvdef * typ * typ                  (* x:t{phi} *)
  | Typ_app      of typ * typ                           (* t t' *) 
  | Typ_dep      of typ * exp                           (* t e *) 
  | Typ_lam      of bvvdef * typ * typ                  (* fun (x:t) => T *)
  | Typ_tlam     of btvdef* kind * typ                  (* fun ('a:k) => T *) 
  | Typ_ascribed of typ * kind                          (* t <: k *)
  | Typ_uvar     of uvar_t * kind                         (* Only needed for unification *)
  | Typ_meta     of meta                                (* Not really in the type language; a way to stash convenient metadata with types *)
  | Typ_unknown                                         (* Initially, every AST node has type unknown *)
and uvar_t = Unionfind.uvar<uvar_basis<typ,kind>>
and meta = 
  | Meta_pos of typ * Range.range   (* user wrote down this type 1 at source position 2 *)
  | Meta_pattern of typ * list<either<typ,exp>>
  | Meta_cases of list<typ>
  | Meta_tid of int
and uvar_basis<'a,'b> = 
  | Uvar of ('a -> 'b -> bool) (* A well-formedness check to ensure that all names are in scope *)
  | Fixed of 'a
  | Delayed of 'a
and exp' =
  | Exp_bvar       of bvar<exp,typ>
  | Exp_fvar       of var<typ> 
  | Exp_constant   of sconst
  | Exp_constr_app of var<typ> * list<either<typ,exp>>
  | Exp_abs        of bvvdef * typ * exp 
  | Exp_tabs       of btvdef * kind * exp            
  | Exp_app        of exp * exp
  | Exp_tapp       of exp * typ             
  | Exp_match      of exp * list<(pat * option<exp> * exp)>      (* optional when clause in each equation *)
  | Exp_ascribed   of exp * typ 
  | Exp_let        of bool * list<(bvvdef * typ * exp)> * exp    (* let (rec?) x1 = e1 AND ... AND xn = en in e *)
  | Exp_primop     of ident * list<exp>
  | Exp_uvar       of uvar_e * typ
and exp = withinfo_t<exp',typ>
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
and kind =
  | Kind_star
  | Kind_prop
  | Kind_erasable
  | Kind_tcon of option<bvdef<typ>> * kind * kind   (* 'a:k -> k' *)
  | Kind_dcon of option<bvvdef> * typ * kind        (* x:t -> k *)
  | Kind_unknown

type formula = typ
type btvar = bvar<typ,kind>
type bvvar = bvar<exp,typ>


type language = 
  | FSharp 
  | CSharp 
  | Fine
  | F7
  | FStar
  | JavaScript
type externqual = | Nullary 
type externref = {language:language;
                  dll:string;
                  namespce:LongIdent;
                  classname:LongIdent;
                  innerclass:string option;
                  extqual:option<externqual>}
type externreference = 
  | ExternRefId of ident
  | ExternRef of externref

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

type letbinding = list<(lident * typ * exp)> (* let recs may have more than one element *)

type sigelt =
  | Sig_tycon          of lident * list<tparam> * kind * list<lident> * list<lident> * list<logic_tag> (* bool is for a prop, list<lident> identifies mutuals *)
  | Sig_typ_abbrev     of lident * list<tparam> * kind * typ
  | Sig_datacon        of lident * typ
  | Sig_val_decl       of lident * typ 
  | Sig_assume         of lident * formula * aqual * atag
  | Sig_logic_function of lident * typ * list<logic_tag>
  | Sig_let            of letbinding * bool
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
let path_of_lid lid = List.map text_of_id lid.lid
let lid_of_ids ids = {lid=ids; str=List.map text_of_id ids |> text_of_path}
let lid_of_path path pos = {lid=List.map (fun s -> mk_ident(s,pos)) path; str=text_of_path path}
let text_of_lid lid = lid.str
let lid_equals l1 l2 = l1.str = l2.str

let withinfo v s r = {v=v; sort=s; p=r}
let withsort v s = withinfo v s dummyRange
let ewithpos v r = {v=v; sort=Typ_unknown; p=r}

let range_of_lid (lid:LongIdent) = 
  let rec last x = match x with
    | [] -> failwith "Empty identifier"
    | [tl] -> tl
    | hd::tl -> last tl in
  let hd = List.hd lid.lid in
  let tl = last lid.lid in
  tl.idRange

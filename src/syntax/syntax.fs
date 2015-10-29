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
and bv = bvar<term>
and fv = var<term> * option<fv_qual>

type lcomp = {
    eff_name: lident;
    res_typ: typ;
    cflags: list<cflags>;
    comp: unit -> comp //a lazy computation
}
type freevars_l = list<bv>
type formula = typ
type formulae = list<typ>

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
type mk_t_a<'a,'b> = option<'b> -> range -> syntax<'a, 'b>
type mk_t = mk_t_a<term',term'>

(*********************************************************************************)
(* Identifiers to/from strings *)
(*********************************************************************************)
let dummyRange = 0L
let withinfo v s r = {v=v; sort=s; p=r}
let withsort v s = withinfo v s dummyRange
let mk_ident (text,range) = {idText=text; idRange=range}
let id_of_text str = mk_ident(str, dummyRange)
let text_of_id (id:ident) = id.idText
let text_of_path path = Util.concat_l "." path
let path_of_text text = String.split ['.'] text
let path_of_ns ns = List.map text_of_id ns
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
let bvd_eq (bvd1:bvdef) (bvd2:bvdef) = bvd1.ppname.idText=bvd2.ppname.idText && bvd1.index=bvd2.index
let order_bvd x y = 
  let i = String.compare x.ppname.idText y.ppname.idText in
  if i = 0 
  then x.index - y.index
  else i
let lid_with_range (lid:LongIdent) (r:Range.range) =
    let id = {lid.ident with idRange=r} in
    {lid with ident=id}
let range_of_lid (lid:LongIdent) = lid.ident.idRange
let range_of_lbname (l:lbname) = match l with
    | Inl x -> x.ppname.idRange
    | Inr l -> range_of_lid l

(*********************************************************************************)
(* Syntax builders *)
(*********************************************************************************)
open FStar.Range

let syn p k f = f k p
let mk_fvs () = Util.mk_ref None
let mk_uvs () = Util.mk_ref None
let new_ftv_set () : set<bv> = Util.new_set (fun x y -> order_bvd x.v y.v) (fun x -> x.v.index + Util.hashcode x.v.ppname.idText)
let new_uv_set ()   = Util.new_set (fun x y -> Unionfind.uvar_id x - Unionfind.uvar_id y) Unionfind.uvar_id
let new_uvt_set () = Util.new_set (fun (x, _) (y, _) -> Unionfind.uvar_id x - Unionfind.uvar_id y) (fun (x, _) -> Unionfind.uvar_id x)
let no_fvs = new_ftv_set()
let no_uvs : uvars = new_uv_set()
let memo_no_uvs = Util.mk_ref (Some no_uvs)
let memo_no_fvs = Util.mk_ref (Some no_fvs)
let freevars_of_list l = List.fold_right Util.set_add l no_fvs
let list_of_freevars (fvs:freevars) = Util.set_elements fvs

(* Constructors for each term form; NO HASH CONSING; just makes all the auxiliary data at each node *)
let mk (t:'a) : mk_t_a<'a,'b> = fun topt r -> {
    n=t;
    pos=r;
    tk=Util.mk_ref topt;
    uvs=mk_uvs(); 
    fvs=mk_fvs()
}
let mk_Tm_app (t1:typ) (args:list<arg>) : mk_t = fun k p ->
    match args with
    | [] -> t1
    | _ -> mk (Tm_app (t1, args)) k p
let extend_app (t:typ) (arg:arg) : mk_t = match t.n with
    | Tm_app(h, args) -> mk (Tm_app(h, args@[arg]))
    | _ -> mk (Tm_app(t, [arg]))
let mk_Tm_abs  ((bs:binders), (t:typ)) k p = 
    match bs with
    | [] -> t
    | _ -> mk (Tm_abs (bs, t)) k p
let mk_Tm_ascribed ((t:typ),(k:term)) (p:range) = 
    mk (Tm_ascribed (t, k, None)) (Some k) p
let mk_Tm_meta     (m:meta) = match m with
    | Meta_pattern(t, _)
    | Meta_named(t, _)
    | Meta_labeled(t, _, _, _)
    | Meta_refresh_label(t, _, _) 
    | Meta_desugared(t, _) -> mk (Tm_meta m) (!t.tk) t.pos
    | Meta_unknown -> mk (Tm_meta m) None dummyRange
let mk_Tm_delayed  ((t:typ),(s:subst_t),(m:memo<typ>)) = 
    match t.n with 
    | Tm_delayed _ -> failwith "NESTED DELAYED TYPES!" 
    | _ -> mk (Tm_delayed(t, s, m))
let mk_Total t : comp = mk (Total t) None t.pos
let mk_Comp (ct:comp_typ) : comp  = mk (Comp ct) None ct.result_typ.pos

let rec pat_vars p = match p.v with
  | Pat_cons(_, ps) ->
    let vars = List.collect (fun (x, _) -> pat_vars x) ps in
    if vars |> nodups bvd_eq
    then vars
    else raise (Error("Pattern variables may not occur more than once", p.p))
  | Pat_var x -> [x.v]
  | Pat_disj ps ->
    let vars = List.map pat_vars ps in
    if not (List.tl vars |> Util.for_all (Util.set_eq order_bvd (List.hd vars)))
    then
      let vars = Util.concat_l ";\n" (vars |>
          List.map (fun v -> Util.concat_l ", " (List.map (fun x -> x.ppname.idText) v))) in
      raise (Error(Util.format1 "Each branch of this pattern binds different variables: %s" vars, p.p))
    else List.hd vars
  | Pat_dot_term _
  | Pat_wild _
  | Pat_constant _ -> []

let mk_lb (x, univs, eff, t, e) = {lbname=x; lbunivs=univs; lbeff=eff; lbtyp=t; lbdef=e}
let mk_subst (s:subst)   = s
let extend_subst x s : subst = x::s
let argpos (x:arg) = (fst x).pos

let tun      = mk_Tm_meta Meta_unknown
let null_id  = mk_ident("_", dummyRange)
let null_bvd = {ppname=null_id; index=0}
let null_bvar (k:term) : bv = {v=null_bvd; sort=k; p=dummyRange}
let mk_binder (a:bv) : binder = a, None
let null_binder t : binder = null_bvar t, None
let iarg t : arg = t, Some Implicit
let arg t : arg = t, None
let is_null_pp (b:bvdef) = b.ppname.idText = null_id.idText
let is_null_bvd (b:bvdef) = is_null_pp b
let is_null_bvar (b:bv) = is_null_bvd b.v
let is_null_binder (b:binder) = is_null_bvar (fst b)

let freevars_of_binders (bs:binders) : freevars =
    List.fold_right (fun (x, _) out -> Util.set_add x out) bs no_fvs

let binders_of_list fvs : binders = (fvs |> List.map (fun t -> t, None))
let binders_of_freevars (fvs:freevars) = Util.set_elements fvs |> binders_of_list
let is_implicit = function Some Implicit -> true | _ -> false
let as_implicit = function true -> Some Implicit | _ -> None

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
open FStar.Ident
open FStar.Const

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
  | U_max   of list<universe>
  | U_bvar  of int
  | U_name  of univ_name
  | U_unif  of Unionfind.uvar<option<universe>>
  | U_unknown
and univ_name = ident

type universe_uvar = Unionfind.uvar<option<universe>>
type univ_names     = list<univ_name>
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
    lbunivs:list<univ_name>; //u1..un
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
   | NT of bv  * term                          (* NT x t: replace a local name with a term t *)
   | UN of int * universe                      (* UN u v: replace universes variable u with universe term v *)
   | UD of univ_name * int                     (* UD x i: replace universe name x with de Bruijn index i *)
and freenames = set<bv>
and uvars    = set<(uvar * typ)>
and syntax<'a,'b> = {
    n:'a;
    tk:memo<'b>;
    pos:Range.range;
    vars:memo<free_vars>;
}
and bv = {
    ppname:ident;  //programmer-provided name for pretty-printing 
    index:int;     //de Bruijn index 0-based, counting up from the binder
    sort:term
}
and fv = var<term> * option<fv_qual>
and free_vars = {
    names:set<bv>;
    uvars:set<(uvar * typ)>;
    univs:set<universe_uvar>;
}

type tscheme = list<univ_name> * typ

type lcomp = {
    eff_name: lident;
    res_typ: typ;
    cflags: list<cflags>;
    comp: unit -> comp //a lazy computation
}
type freenames_l = list<bv>
type formula = typ
type formulae = list<typ>

type qualifier =
  | Private
  | Assumption
  | New
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
    qualifiers  :list<qualifier>;
    mname       :lident;
    univs       :univ_names;
    binders     :binders;
    signature   :term;
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
  | Sig_inductive_typ          of lident                   //type l forall u1..un. (x1:t1) ... (xn:tn) : t 
                       * univ_names                 //u1..un
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
                       * univ_names                  //universe variables
                       * typ 
                       * lident                     //the inductive type of the value this constructs
                       * int                        //and the number of parameters of the inductive
                       * list<qualifier> 
                       * list<lident>               //mutually defined types 
                       * Range.range
  | Sig_declare_typ       of lident 
                       * univ_names
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
  | Sig_effect_abbrev  of lident * univ_names * binders * comp * list<qualifier> * Range.range
  | Sig_pragma         of pragma * Range.range
type sigelts = list<sigelt>

type modul = {
  name: lident;
  declarations: sigelts;
  exports: sigelts;
  is_interface:bool
}
type path = list<string>
type subst = list<subst_elt>
type mk_t_a<'a,'b> = option<'b> -> range -> syntax<'a, 'b>
type mk_t = mk_t_a<term',term'>

(*********************************************************************************)
(* Identifiers to/from strings *)
(*********************************************************************************)
let withinfo v s r = {v=v; sort=s; p=r}
let withsort v s = withinfo v s dummyRange

let bv_eq (bv1:bv) (bv2:bv) = bv1.ppname.idText=bv2.ppname.idText && bv1.index=bv2.index
let order_bv x y = 
  let i = String.compare x.ppname.idText y.ppname.idText in
  if i = 0 
  then x.index - y.index
  else i

let range_of_lbname (l:lbname) = match l with
    | Inl x -> x.ppname.idRange
    | Inr l -> range_of_lid l
let range_of_bv x = x.ppname.idRange

(*********************************************************************************)
(* Syntax builders *)
(*********************************************************************************)
open FStar.Range

let syn p k f = f k p
let mk_fvs () = Util.mk_ref None
let mk_uvs () = Util.mk_ref None
let new_bv_set () : set<bv> = Util.new_set order_bv (fun x -> x.index + Util.hashcode x.ppname.idText)
let new_uv_set () : uvars   = Util.new_set (fun (x, _) (y, _) -> Unionfind.uvar_id x - Unionfind.uvar_id y)  
                                           (fun (x, _) -> Unionfind.uvar_id x)
let new_universe_uvar_set () : set<universe_uvar> = 
    Util.new_set (fun x y -> Unionfind.uvar_id x - Unionfind.uvar_id y)  
                 (fun x -> Unionfind.uvar_id x)
let no_names  = new_bv_set()
let no_uvs : uvars = new_uv_set()
let no_universe_uvars = new_universe_uvar_set()
let memo_no_uvs = Util.mk_ref (Some no_uvs)
let memo_no_names = Util.mk_ref (Some no_names)
let freenames_of_list l = List.fold_right Util.set_add l no_names
let list_of_freenames (fvs:freenames) = Util.set_elements fvs

(* Constructors for each term form; NO HASH CONSING; just makes all the auxiliary data at each node *)
let mk (t:'a) : mk_t_a<'a,'b> = fun topt r -> {
    n=t;
    pos=r;
    tk=Util.mk_ref topt;
    vars=Util.mk_ref None;
}
let bv_to_tm   bv :term = mk (Tm_bvar bv) (Some bv.sort.n) (range_of_bv bv)
let bv_to_name bv :term = mk (Tm_name bv) (Some bv.sort.n) (range_of_bv bv)
let mk_Tm_app (t1:typ) (args:list<arg>) : mk_t = fun k p ->
    match args with
    | [] -> t1
    | _ -> mk (Tm_app (t1, args)) k p
let mk_Tm_uinst (t:term) = function
    | [] -> t
    | us ->
      match t.n with 
        | Tm_fvar _ ->  mk (Tm_uinst(t, us)) None t.pos
        | _ -> failwith "Unexpected universe instantiation"

let extend_app t arg kopt r = match t.n with 
    | Tm_app(head, args) -> mk_Tm_app head (args@[arg]) kopt r
    | _ -> mk_Tm_app t [arg] kopt r
let mk_Tm_delayed lr pos : term = mk (Tm_delayed(lr, Util.mk_ref None)) None pos
let mk_Total t : comp = mk (Total t) None t.pos
let mk_Comp (ct:comp_typ) : comp  = mk (Comp ct) None ct.result_typ.pos
let mk_lb (x, univs, eff, t, e) = {lbname=x; lbunivs=univs; lbeff=eff; lbtyp=t; lbdef=e}
let mk_subst (s:subst)   = s
let extend_subst x s : subst = x::s
let argpos (x:arg) = (fst x).pos

let tun : term = mk (Tm_unknown) None dummyRange
let teff : term = mk (Tm_constant Const_effect) None dummyRange
let is_teff (t:term) = match t.n with 
    | Tm_constant Const_effect -> true
    | _ -> false
let null_id  = mk_ident("_", dummyRange)
let null_bv k = {ppname=null_id; index=0; sort=k}
let mk_binder (a:bv) : binder = a, None
let null_binder t : binder = null_bv t, None
let iarg t : arg = t, Some Implicit
let arg t : arg = t, None
let is_null_bv (b:bv) = b.ppname.idText = null_id.idText
let is_null_binder (b:binder) = is_null_bv (fst b)

let freenames_of_binders (bs:binders) : freenames =
    List.fold_right (fun (x, _) out -> Util.set_add x out) bs no_names

let binders_of_list fvs : binders = (fvs |> List.map (fun t -> t, None))
let binders_of_freenames (fvs:freenames) = Util.set_elements fvs |> binders_of_list
let is_implicit = function Some Implicit -> true | _ -> false
let as_implicit = function true -> Some Implicit | _ -> None

let pat_bvs (p:pat) : list<bv> = 
    let rec aux b p = match p.v with
        | Pat_dot_term _
        | Pat_wild _
        | Pat_constant _ -> b
        | Pat_var x -> x::b
        | Pat_cons(_, pats) -> List.fold_left (fun b (p, _) -> aux b p) b pats
        | Pat_disj(p::_) -> aux b p
        | Pat_disj [] -> failwith "impossible" in
  aux [] p
         
(* Gen sym *)
let gen_reset = 
    let x = ref 0 in
    let gen () = incr x; !x in
    let reset () = x := 0 in
    gen, reset
let next_id = fst gen_reset
let reset_gensym = snd gen_reset
let freshen_bv bv = {bv with index=next_id()}
let range_of_ropt = function 
    | None -> dummyRange
    | Some r -> r
let gen_bv : string -> option<Range.range> -> typ -> bv = fun s r t ->
  let id = mk_ident(s, range_of_ropt r) in
  {ppname=id; index=next_id(); sort=t}
let new_bv ropt t = gen_bv "x" ropt t
let new_univ_name ropt = 
    let id = next_id() in 
    mk_ident (Util.string_of_int id, range_of_ropt ropt)
let mkbv x y t  = {ppname=x;index=y;sort=t}
let lbname_eq l1 l2 = match l1, l2 with
  | Inl x, Inl y -> bv_eq x y
  | Inr l, Inr m -> lid_equals l m
  | _ -> false
let fv_eq ((fv1, _):fv) ((fv2, _):fv)  = lid_equals fv1.v fv2.v
let set_bv_range bv r = {bv with ppname=mk_ident(bv.ppname.idText, r)}
let fv l dc : fv = withinfo l tun (range_of_lid l), dc
let fv_to_tm (fv:fv) : term = mk (Tm_fvar fv) None (range_of_lid (fst fv).v)
let fvar dc l r : term = mk (Tm_fvar(fv (set_lid_range l r) dc)) None r

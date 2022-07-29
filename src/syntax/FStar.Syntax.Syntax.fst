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
module FStar.Syntax.Syntax
(* Prims is used for bootstrapping *)
open Prims
open FStar.Pervasives
open FStar.Compiler.Effect
open FStar.Compiler.List
(* Type definitions for the core AST *)

open FStar
open FStar.Compiler
open FStar.Compiler.Util
open FStar.Compiler.Range
open FStar.Ident
open FStar.Const
open FStar.Compiler.Dyn
module O = FStar.Options
module PC = FStar.Parser.Const
open FStar.VConfig

// This is set in FStar.Main.main, where all modules are in-scope.
let lazy_chooser : ref (option (lazy_kind -> lazyinfo -> term)) = mk_ref None

let mod_name (m: modul) = m.name

let contains_reflectable (l: list qualifier): bool =
    Util.for_some (function Reflectable _ -> true | _ -> false) l

(*********************************************************************************)
(* Identifiers to/from strings *)
(*********************************************************************************)
let withinfo v r = {v=v; p=r}
let withsort v = withinfo v dummyRange

let bv_eq (bv1:bv) (bv2:bv) =
    ident_equals bv1.ppname bv2.ppname && bv1.index=bv2.index

let order_bv x y =
  let i = String.compare (string_of_id x.ppname) (string_of_id y.ppname) in
  if i = 0
  then x.index - y.index
  else i

let order_ident x y = String.compare (string_of_id x) (string_of_id y)
let order_fv x y = String.compare (string_of_lid x) (string_of_lid y)

let range_of_lbname (l:lbname) = match l with
    | Inl x -> range_of_id x.ppname
    | Inr fv -> range_of_lid fv.fv_name.v
let range_of_bv x = range_of_id x.ppname

let set_range_of_bv x r = {x with ppname = set_id_range r x.ppname }


(* Helpers *)
let on_antiquoted (f : (term -> term)) (qi : quoteinfo) : quoteinfo =
    let aq = List.map (fun (bv, t) -> (bv, f t)) qi.antiquotes in
    { qi with antiquotes = aq }

let lookup_aq (bv : bv) (aq : antiquotations) : option term =
    match List.tryFind (fun (bv', _) -> bv_eq bv bv') aq with
    | Some (_, e) -> Some e
    | None -> None

(*********************************************************************************)
(* Syntax builders *)
(*********************************************************************************)

let syn p k f = f k p
let mk_fvs () = Util.mk_ref None
let mk_uvs () = Util.mk_ref None
let new_bv_set () : set bv = Util.new_set order_bv
let new_id_set () : set ident = Util.new_set order_ident
let new_fv_set () :set lident = Util.new_set order_fv
let order_univ_name x y = String.compare (Ident.string_of_id x) (Ident.string_of_id y)
let new_universe_names_set () : set univ_name = Util.new_set order_univ_name

let eq_binding b1 b2 =
    match b1, b2 with
    | Binding_var bv1, Binding_var bv2 -> bv_eq bv1 bv2
    | Binding_lid (lid1, _), Binding_lid (lid2, _) -> lid_equals lid1 lid2
    | Binding_univ u1, Binding_univ u2 -> ident_equals u1 u2
    | _ -> false

let no_names  = new_bv_set()
let no_fvars  = new_fv_set()
let no_universe_names = new_universe_names_set ()
//let memo_no_uvs = Util.mk_ref (Some no_uvs)
//let memo_no_names = Util.mk_ref (Some no_names)
let freenames_of_list l = List.fold_right Util.set_add l no_names
let list_of_freenames (fvs:freenames) = Util.set_elements fvs

(* Constructors for each term form; NO HASH CONSING; just makes all the auxiliary data at each node *)
let mk (t:'a) r = {
    n=t;
    pos=r;
    vars=Util.mk_ref None;
    hash_code=Util.mk_ref None;
}

let bv_to_tm   bv :term = mk (Tm_bvar bv) (range_of_bv bv)
let bv_to_name bv :term = mk (Tm_name bv) (range_of_bv bv)
let binders_to_names (bs:binders) : list term = bs |> List.map (fun b -> bv_to_name b.binder_bv)
let mk_Tm_app (t1:typ) (args:list arg) p =
    match args with
    | [] -> t1
    | _ -> mk (Tm_app (t1, args)) p
let mk_Tm_uinst (t:term) (us:universes) =
  match t.n with
  | Tm_fvar _ ->
    begin match us with
    | [] -> t
    | us -> mk (Tm_uinst(t, us)) t.pos
    end
  | _ -> failwith "Unexpected universe instantiation"

let extend_app_n t args' r = match t.n with
    | Tm_app(head, args) -> mk_Tm_app head (args@args') r
    | _ -> mk_Tm_app t args' r
let extend_app t arg r = extend_app_n t [arg] r
let mk_Tm_delayed lr pos : term = mk (Tm_delayed lr) pos
let mk_Total' t  u: comp  = mk (Total(t, u)) t.pos
let mk_GTotal' t u: comp = mk (GTotal(t, u)) t.pos
let mk_Total t = mk_Total' t None
let mk_GTotal t = mk_GTotal' t None
let mk_Comp (ct:comp_typ) : comp  = mk (Comp ct) ct.result_typ.pos
let mk_lb (x, univs, eff, t, e, attrs, pos) = {
    lbname=x;
    lbunivs=univs;
    lbtyp=t;
    lbeff=eff;
    lbdef=e;
    lbattrs=attrs;
    lbpos=pos;
  }

let mk_Tac t =
    mk_Comp ({ comp_univs = [U_zero];
               effect_name = PC.effect_Tac_lid;
               result_typ = t;
               effect_args = [];
               flags = [SOMETRIVIAL; TRIVIAL_POSTCONDITION];
            })

let default_sigmeta = { sigmeta_active=true; sigmeta_fact_db_ids=[]; sigmeta_admit=false }
let mk_sigelt (e: sigelt') = { sigel = e; sigrng = Range.dummyRange; sigquals=[]; sigmeta=default_sigmeta; sigattrs = [] ; sigopts = None }
let mk_subst (s:subst_t)   = s
let extend_subst x s : subst_t = x::s
let argpos (x:arg) = (fst x).pos

let tun : term = mk (Tm_unknown) dummyRange
let teff : term = mk (Tm_constant Const_effect) dummyRange
let is_teff (t:term) = match t.n with
    | Tm_constant Const_effect -> true
    | _ -> false
let is_type (t:term) = match t.n with
    | Tm_type _ -> true
    | _ -> false
let null_id  = mk_ident("_", dummyRange)
let null_bv k = {ppname=null_id; index=0; sort=k}
let mk_binder_with_attrs bv aqual attrs = {
  binder_bv = bv;
  binder_qual = aqual;
  binder_attrs = attrs
}
let mk_binder a = mk_binder_with_attrs a None []
let null_binder t : binder = mk_binder (null_bv t)
let imp_tag = Implicit false
let iarg t : arg = t, Some ({ aqual_implicit = true; aqual_attributes = [] })
let as_arg t : arg = t, None
let is_null_bv (b:bv) = string_of_id b.ppname = string_of_id null_id
let is_null_binder (b:binder) = is_null_bv b.binder_bv

let is_top_level = function
    | {lbname=Inr _}::_ -> true
    | _ -> false

let freenames_of_binders (bs:binders) : freenames =
    List.fold_right (fun b out -> Util.set_add b.binder_bv out) bs no_names

let binders_of_list fvs : binders = (fvs |> List.map (fun t -> mk_binder t))
let binders_of_freenames (fvs:freenames) = Util.set_elements fvs |> binders_of_list
let is_bqual_implicit = function Some (Implicit _) -> true | _ -> false
let is_aqual_implicit = function Some { aqual_implicit = b } -> b | _ -> false
let is_bqual_implicit_or_meta = function Some (Implicit _) | Some (Meta _) -> true | _ -> false
let as_bqual_implicit = function true -> Some imp_tag | _ -> None
let as_aqual_implicit = function true -> Some ({aqual_implicit=true; aqual_attributes=[]}) | _ -> None
let pat_bvs (p:pat) : list bv =
    let rec aux b p = match p.v with
        | Pat_dot_term _
        | Pat_constant _ -> b
        | Pat_wild x
        | Pat_var x -> x::b
        | Pat_cons(_, _, pats) -> List.fold_left (fun b (p, _) -> aux b p) b pats
    in
  List.rev <| aux [] p

(* Gen sym *)
let range_of_ropt = function
    | None -> dummyRange
    | Some r -> r
let gen_bv : string -> option Range.range -> typ -> bv = fun s r t ->
  let id = mk_ident(s, range_of_ropt r) in
  {ppname=id; index=Ident.next_id(); sort=t}
let new_bv ropt t = gen_bv Ident.reserved_prefix ropt t

let freshen_bv bv =
    if is_null_bv bv
    then new_bv (Some (range_of_bv bv)) bv.sort
    else {bv with index=Ident.next_id()}

let freshen_binder (b:binder) = { b with binder_bv = freshen_bv b.binder_bv }

let new_univ_name ropt =
    let id = Ident.next_id() in
    mk_ident (Ident.reserved_prefix ^ Util.string_of_int id, range_of_ropt ropt)
let lbname_eq l1 l2 = match l1, l2 with
  | Inl x, Inl y -> bv_eq x y
  | Inr l, Inr m -> lid_equals l m
  | _ -> false
let fv_eq fv1 fv2 = lid_equals fv1.fv_name.v fv2.fv_name.v
let fv_eq_lid fv lid = lid_equals fv.fv_name.v lid

let set_bv_range bv r = {bv with ppname = set_id_range r bv.ppname}

let lid_as_fv l dd dq : fv = {
    fv_name=withinfo l (range_of_lid l);
    fv_delta=dd;
    fv_qual =dq;
}
let fv_to_tm (fv:fv) : term = mk (Tm_fvar fv) (range_of_lid fv.fv_name.v)
let fvar l dd dq =  fv_to_tm (lid_as_fv l dd dq)
let lid_of_fv (fv:fv) = fv.fv_name.v
let range_of_fv (fv:fv) = range_of_lid (lid_of_fv fv)
let set_range_of_fv (fv:fv) (r:Range.range) =
    {fv with fv_name={fv.fv_name with v=Ident.set_lid_range (lid_of_fv fv) r}}
let has_simple_attribute (l: list term) s =
  List.existsb (function
    | { n = Tm_constant (Const_string (data, _)) } when data = s ->
        true
    | _ ->
        false
  ) l

// Compares the SHAPE of the patterns, *ignoring bound variables and universes*
let rec eq_pat (p1 : pat) (p2 : pat) : bool =
    match p1.v, p2.v with
    | Pat_constant c1, Pat_constant c2 -> eq_const c1 c2
    | Pat_cons (fv1, us1, as1), Pat_cons (fv2, us2, as2) ->
        if fv_eq fv1 fv2
        && List.length as1 = List.length as2
        then List.forall2 (fun (p1, b1) (p2, b2) -> b1 = b2 && eq_pat p1 p2) as1 as2
          && (match us1, us2 with
              | None, None -> true
              | Some us1, Some us2 -> 
                List.length us1 = List.length us2
              | _ -> false)
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
let fvconst l = lid_as_fv l delta_constant None
let tconst l = mk (Tm_fvar (fvconst l)) Range.dummyRange
let tabbrev l = mk (Tm_fvar(lid_as_fv l (Delta_constant_at_level 1) None)) Range.dummyRange
let tdataconstr l = fv_to_tm (lid_as_fv l delta_constant (Some Data_ctor))
let t_unit      = tconst PC.unit_lid
let t_bool      = tconst PC.bool_lid
let t_int       = tconst PC.int_lid
let t_string    = tconst PC.string_lid
let t_exn       = tconst PC.exn_lid
let t_real      = tconst PC.real_lid
let t_float     = tconst PC.float_lid
let t_char      = tabbrev PC.char_lid
let t_range     = tconst PC.range_lid
let t_vconfig   = tconst PC.vconfig_lid
let t_term      = tconst PC.term_lid
let t_term_view = tabbrev PC.term_view_lid
let t_order     = tconst PC.order_lid
let t_decls     = tabbrev PC.decls_lid
let t_binder    = tconst PC.binder_lid
let t_binders   = tconst PC.binders_lid
let t_bv        = tconst PC.bv_lid
let t_fv        = tconst PC.fv_lid
let t_norm_step = tconst PC.norm_step_lid
let t_tac_of a b =
    mk_Tm_app (mk_Tm_uinst (tabbrev PC.tac_lid) [U_zero; U_zero])
              [as_arg a; as_arg b] Range.dummyRange
let t_tactic_of t =
    mk_Tm_app (mk_Tm_uinst (tabbrev PC.tactic_lid) [U_zero])
              [as_arg t] Range.dummyRange

let t_tactic_unit = t_tactic_of t_unit

(*
 * AR: what's up with all the U_zero below?
 *)
let t_list_of t = mk_Tm_app
  (mk_Tm_uinst (tabbrev PC.list_lid) [U_zero])
  [as_arg t]
  Range.dummyRange
let t_option_of t = mk_Tm_app
  (mk_Tm_uinst (tabbrev PC.option_lid) [U_zero])
  [as_arg t]
  Range.dummyRange
let t_tuple2_of t1 t2 = mk_Tm_app
  (mk_Tm_uinst (tabbrev PC.lid_tuple2) [U_zero;U_zero])
  [as_arg t1; as_arg t2]
  Range.dummyRange
let t_tuple3_of t1 t2 t3 = mk_Tm_app
  (mk_Tm_uinst (tabbrev PC.lid_tuple3) [U_zero;U_zero;U_zero])
  [as_arg t1; as_arg t2; as_arg t3]
  Range.dummyRange
let t_either_of t1 t2 = mk_Tm_app
  (mk_Tm_uinst (tabbrev PC.either_lid) [U_zero;U_zero])
  [as_arg t1; as_arg t2]
  Range.dummyRange

let unit_const_with_range r = mk (Tm_constant FStar.Const.Const_unit) r
let unit_const = unit_const_with_range Range.dummyRange

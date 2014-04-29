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
// (c) Microsoft Corporation. All rights reserved
module Microsoft.FStar.Absyn.Util

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Profiling

let handle_err warning ret e = 
  match e with
    | Error(msg, r) ->
        Util.print_string (Util.format3 "%s : %s : %s\n" (Range.string_of_range r) (if warning then "Warning" else "Error") msg);
        ret
    | NYI s -> 
        Util.print_string (Util.format1 "Feature not yet implemented: %s" s); 
        ret
    | Err s -> 
        Util.print_string (Util.format1 "Error: %s" s)
    | _ -> raise e

let handleable = function
  | Error _
  | NYI _ 
  | Err _ -> true
  | _ -> false

(********************************************************************************)
(******************** Compressing out unification vars **************************)
(********************************************************************************)          

let compress_kind = Visit.compress_kind
let compress_typ  = Visit.compress
let compress_exp  = Visit.compress_exp 

(********************************************************************************)
(**************************Utilities for identifiers ****************************)
(********************************************************************************)

let gensym = 
  let ctr = mk_ref 0 in 
  (fun () -> Util.format1 "x_%s" (Util.string_of_int (incr ctr; !ctr)))
    
let rec gensyms x = match x with
  | 0 -> []
  | n -> gensym ()::gensyms (n-1)
    
let genident r = 
  let sym = gensym () in
  match r with 
    | None -> mk_ident(sym, dummyRange)
    | Some r -> mk_ident(sym, r)

let range_of_bvd x = x.ppname.idRange
let inst () = mk_ref None
let mkbvd (x,y) = {ppname=x;realname=y;instantiation=inst()}
let setsort w t = {v=w.v; sort=t; p=w.p}
let withinfo e s r = {v=e; sort=s; p=r}
let withsort e s   = withinfo e s dummyRange
let bvar_ppname bv = bv.v.ppname 
let bvar_realname bv = bv.v.realname
let bvar_eq (bv1:bvar<'a,'b>) (bv2:bvar<'a,'b>) = 
  (bvar_realname bv1).idText = (bvar_realname bv2).idText
let bvd_eq bvd1 bvd2 = bvd1.realname.idText=bvd2.realname.idText
let lbname_eq l1 l2 = match l1, l2 with
  | Inl x, Inl y -> bvd_eq x y
  | Inr l, Inr m -> lid_equals l m
  | _ -> false
let fvar_eq fv1 fv2  = lid_equals fv1.v fv2.v
let bvd_to_bvar_s bvd sort = {v=bvd; sort=sort; p=bvd.ppname.idRange}
let bvar_to_bvd bv = bv.v
let btvar_to_typ bv  = Typ_btvar bv
let bvd_to_typ bvd k = btvar_to_typ (bvd_to_bvar_s bvd k)
let bvar_to_exp bv   =  Exp_bvar bv
let bvd_to_exp bvd t = bvar_to_exp (bvd_to_bvar_s bvd t)
let new_bvd ropt = let id = genident ropt in mkbvd (id,id)
let gen_bvar sort = let bvd = (new_bvd None) in bvd_to_bvar_s bvd sort
let gen_bvar_p r sort = let bvd = (new_bvd (Some r)) in bvd_to_bvar_s bvd sort
let bvdef_of_str s = let id = id_of_text s in mkbvd(id, id)
let set_bvd_range bvd r = {ppname=mk_ident(bvd.ppname.idText, r);
                           realname=mk_ident(bvd.realname.idText, r);
                           instantiation=bvd.instantiation}
let set_lid_range l r = 
  let ids = (l.ns@[l.ident]) |> List.map (fun i -> mk_ident(i.idText, r)) in
  lid_of_ids ids
let fv l = withinfo l Typ_unknown (range_of_lid l)
let fvar l r =  Exp_fvar(fv (set_lid_range l r), false)
let ftv l = Typ_const (withinfo l Kind_unknown (range_of_lid l))
let order_bvd x y = match x, y with 
  | Inl _, Inr _ -> -1
  | Inr _, Inl _ -> 1
  | Inl x, Inl y -> String.compare x.ppname.idText y.ppname.idText
  | Inr x, Inr y -> String.compare x.ppname.idText y.ppname.idText


(********************************************************************************)
(****************Simple utils on the local structure of a term ******************)
(********************************************************************************)

let rec ascribe e t = match e with 
  | Exp_ascribed (e, _) -> ascribe e t
  | _ -> withsort (Exp_ascribed(e, t)) t
    
let rec unascribe e = match e with 
  | Exp_ascribed (e, _) -> unascribe e 
  | _ -> e

let rec ascribe_typ t k = match t with 
  |  Typ_ascribed (t', _) -> ascribe_typ t' k
  | _ -> Typ_ascribed(t, k)
    
let rec unascribe_typ t = match t with 
  | Typ_ascribed (t, _) -> unascribe_typ t
  | _ -> t

let rec unrefine t = match t with 
  | Typ_refine(x, t, _) -> unrefine t
  | _ -> t

let pos e r' = match e with 
  | Exp_meta(Meta_info(_, _, r)) -> r
  | _ -> r'

let rec pre_typ t = match compress_typ t with 
  | Typ_refine(_, t, _) 
  | Typ_ascribed(t, _) -> pre_typ t
  | t -> t

(* If the input type is a Typ_app, walks the Typ_app tree and
   flattens the type parameters. Does not recursively drill into
   other kinds of types. *)
let flatten_typ_apps : typ -> typ * (list<either<typ,exp>>) =
  let rec aux acc t = 
    match pre_typ t with
      | Typ_app(t1, t2, _) -> aux (Inl t2::acc) t1 
      | Typ_dep(t1, v, _) -> aux (Inr v::acc) t1
      | _              -> t, acc in
  (fun t -> aux [] t)
    
let destruct typ lid = 
  match flatten_typ_apps typ with 
    | Typ_const tc, args when lid_equals tc.v lid -> Some args
    | _ -> None

let rec lids_of_sigelt se = match se with 
  | Sig_bundle ses -> List.collect lids_of_sigelt ses
  | Sig_tycon (lid, _, _, _, _, _)    
  | Sig_typ_abbrev  (lid, _, _, _)
  | Sig_datacon (lid, _, _)
  | Sig_val_decl (lid, _, _, _) 
  | Sig_assume (lid, _, _, _)
  | Sig_logic_function (lid, _, _) -> [lid]
  | Sig_let((_, lbs)) -> List.map (function 
    | (Inr l, _, _) -> l
    | (Inl x, _, _) -> failwith (Util.format1 "Impossible: got top-level letbinding with name %s" x.ppname.idText)) lbs
  | Sig_main _ -> []
    
let lid_of_sigelt se = List.hd <| lids_of_sigelt se
let range_of_sigelt x = range_of_lid <| lid_of_sigelt x
let range_of_typ t def = match t with 
  | Typ_meta(Meta_pos(_, r)) -> r
  | _ -> def
let range_of_lb = function
  | (Inl x, _, _) -> range_of_bvd x
  | (Inr l, _, _) -> range_of_lid l 

let mk_curried_app e e_or_t = 
  List.fold_left (fun f -> function
    | Inl t -> Exp_tapp(f, t) 
    | Inr (e, imp) -> Exp_app(f, e, imp))  e e_or_t 

let uncurry_app e =
  let rec aux e out = match compress_exp e with 
    | Exp_app(e1, e2, imp) -> aux e1 (Inr (e2, imp)::out)
    | Exp_tapp(e1, t) -> aux e1 (Inl t::out)
    | _ -> e, out in
  aux e []

let mk_data l args = 
  Exp_meta(Meta_desugared(mk_curried_app (fvar l (range_of_lid l)) args, Data_app))

let destruct_app =
    let rec destruct acc (e : exp) =
        match e with
        | Exp_app (e1, e2, b) -> destruct ((e2, b) :: acc) e1
        | Exp_ascribed (e, _) -> destruct acc e
        | Exp_meta (Meta_info (e, _, _)) -> destruct acc e
        | _ -> (e, acc)
    in

    fun e -> destruct [] e

let destruct_fun =
    let rec destruct acc (e : exp) =
        match e with
        | Exp_abs (x, ty, e) -> destruct ((x, ty) :: acc) e
        | Exp_ascribed (e, _) -> destruct acc e
        | Exp_meta (Meta_info (e, _, _)) -> destruct acc e
        | _ -> (List.rev acc, e)
    in

    fun e -> destruct [] e

(********************************************************************************)
(******************************** Syntactic values ******************************)
(********************************************************************************)

let rec is_value e = 
  let is_val e = match compress_exp e with 
    | Exp_constant _
    | Exp_bvar _
    | Exp_fvar _ 
    | Exp_abs _ 
    | Exp_tabs _ -> true
    | Exp_primop(id, el) -> 
        if (id.idText = "op_AmpAmp" ||
            id.idText = "op_BarBar" ||
            id.idText = "_dummy_op_Negation")
        then Util.for_all is_value el
        else false
    | Exp_ascribed(e, _) -> is_value e
    | Exp_app _ -> is_data e
    | _ -> false in 
    (is_val e) || (is_logic_function e)

and is_data e = match compress_exp e with 
  | Exp_fvar(_, b) -> b
  | Exp_app(e, e', _) -> is_value e' && is_data e
  | Exp_tapp(e, _) -> is_data e
  | Exp_ascribed(e, _) -> is_data e
  | _ -> false

and is_logic_function e = match compress_exp e with
  (* | Exp_tapp(e1, _) -> is_logic_function e1 *)
  | Exp_app(e1, e2, _) -> is_value e2 && is_logic_function e1
  | Exp_fvar(v, _) ->
      lid_equals v.v Const.op_And ||
        lid_equals v.v Const.op_Or ||
        lid_equals v.v Const.op_Negation ||
        lid_equals v.v Const.op_Addition ||
        lid_equals v.v Const.op_Subtraction ||
        lid_equals v.v Const.op_Multiply
  | Exp_ascribed(e, _) -> is_logic_function e
  | _ -> false     
   

(********************************************************************************)
(************** Collecting all unification variables in a type ******************)
(********************************************************************************)

type uvars = {
  uvars_k: list<uvar_k>;
  uvars_t: list<(uvar_t*kind)>;
  uvars_e: list<(uvar_e*typ)>
  }
let empty_uvars = {uvars_k=[]; uvars_t=[]; uvars_e=[]}
let collect_uvars_k uvs k = match k with 
  | Kind_uvar uv -> 
      (match List.tryFind (Unionfind.equivalent uv) uvs.uvars_k with 
          | Some _ -> uvs, k
          | None -> {uvs with uvars_k=uv::uvs.uvars_k}, k)
  | _ -> uvs, k
let collect_uvars_t uvs t : uvars * typ = match t with 
    | Typ_uvar (uv, k) -> 
        (match List.tryFind (fun (uv', _) -> Unionfind.equivalent uv uv') uvs.uvars_t with 
          | Some _ -> uvs, t
          | None -> {uvs with uvars_t=(uv,k)::uvs.uvars_t}, t)
      | _ -> uvs, t 
let collect_uvars_e uvs e : uvars * exp = match e with 
    | Exp_uvar (uv, t) -> 
        (match List.tryFind (fun (uv', _) -> Unionfind.equivalent uv uv') uvs.uvars_e with 
          | Some _ -> uvs, e
          | None -> {uvs with uvars_e=(uv,t)::uvs.uvars_e}, e)
    | _ -> uvs, e 
let uvars_in_kind k : uvars = 
  fst <| Visit.visit_kind_simple collect_uvars_k collect_uvars_t collect_uvars_e empty_uvars k
let uvars_in_typ t : uvars = 
  fst <| Visit.visit_typ_simple collect_uvars_k collect_uvars_t collect_uvars_e empty_uvars t
let uvars_in_exp e : uvars = 
  fst <| Visit.visit_exp_simple collect_uvars_k collect_uvars_t collect_uvars_e empty_uvars e

(********************************************************************************)
(**************************** Free type/term variables **************************)
(********************************************************************************)

type freevars = (list<btvar> * list<bvvar>)
type boundvars = (list<btvdef> * list<bvvdef>)
let is_bound_tv ((btvs, _):boundvars) (bv:btvar) = 
  Util.for_some (fun bvd' -> bvd_eq bvd' bv.v) btvs 
let is_bound_xv ((_, bxvs):boundvars) (bv:bvvar) = 
  Util.for_some (fun bvd' -> bvd_eq bvd' bv.v) bxvs 
let fv_fold_t (out:freevars) (benv:boundvars) (t:typ) : (freevars * typ) =
  let (ftvs, fxvs) = out in
  match t with
    | Typ_btvar bv -> 
      if is_bound_tv benv bv then out, t
      else (bv::ftvs, fxvs), t
    | _ -> out, t 
let fv_fold_e (out:freevars) (benv:boundvars) (e:exp) : (freevars * exp) =
  let (ftvs, fxvs) = out in
  match e with
    | Exp_bvar bv ->
      if is_bound_xv benv bv then out, e (* let _ = pr "Bvar %s is bound, where env is %s\n" (strBvar bv) (strBenv benv) in *)
      else (ftvs, bv::fxvs), e      (* let _ = pr "Bvar %s is free, where env is %s\n" (strBvar bv) (strBenv benv) in *)
    | _ -> out, e 
let ext_fv_env ((btvs, bxvs):boundvars) : either<btvar,bvvar> -> (boundvars * either<btvdef, bvvdef>) =
  function 
    | Inl tv -> (tv.v::btvs, bxvs), Inl tv.v
    | Inr xv -> (btvs, xv.v::bxvs), Inr xv.v 
let fold_kind_noop env benv k = (env, k)

let freevars_kind : kind -> freevars = 
  fun k -> fst <| Visit.visit_kind fold_kind_noop fv_fold_t fv_fold_e (fun _ e -> e) ext_fv_env ([], []) ([], []) k
      
let freevars_typ : typ -> freevars = 
  fun t -> fst <| Visit.visit_typ fold_kind_noop fv_fold_t fv_fold_e (fun _ e -> e) ext_fv_env ([], []) ([], []) t
      
let freevars_exp : exp -> freevars =
  fun e -> fst <| Visit.visit_exp fold_kind_noop fv_fold_t fv_fold_e (fun _ e -> e) ext_fv_env ([], []) ([], []) e

(********************************************************************************)
(************************** Type/term substitutions *****************************)
(********************************************************************************)

type subst = list<either<(btvdef*typ), (bvvdef*exp)>>
type subst_map = Util.smap<either<typ,exp>>
let mk_subst_map (s:subst) = 
  let t = Util.smap_create(List.length s) in
  s |> List.iter (function 
    | Inl(a, ty) -> Util.smap_add t a.realname.idText (Inl ty)
    | Inr(x, e) -> Util.smap_add t x.realname.idText (Inr e));
  t
let lift_subst f = (fun () x -> (), f x)
(* Should never call these ones directly *)
let rec subst_kind' (s:subst_map) (k:kind) : kind =
  snd (Visit.visit_kind_simple
         (fun e k -> e,k)
         (lift_subst (subst_tvar s))
         (lift_subst (subst_xvar s))
         () k)
and subst_typ' (s:subst_map) (t:typ) : typ =
  snd (Visit.visit_typ_simple
         (fun e k -> e,k)
         (lift_subst (subst_tvar s))
         (lift_subst (subst_xvar s))
         () t)
and subst_exp' (s:subst_map) (e:exp) : exp =
  snd (Visit.visit_exp_simple
         (fun e k -> e,k)
         (lift_subst (subst_tvar s))
         (lift_subst (subst_xvar s))
         () e)
and subst_tvar (s:subst_map) (t:typ) : typ =
  let find_typ btv = match Util.smap_try_find s btv.realname.idText with 
    | Some (Inl l) -> Some l
    | _ ->  None in
  match t with
    | Typ_btvar btv ->
      begin
        match find_typ btv.v with
          | Some t -> t
          | _ ->
            let sort' = subst_kind' s btv.sort in
            Typ_btvar (setsort btv sort')
      end
    | _ -> t
and subst_xvar (s:subst_map) (e:exp) : exp =
  let find_exp bv =  match Util.smap_try_find s bv.realname.idText with 
    | Some (Inr e) -> Some e
    | _ ->  None in
  match e with
    | Exp_bvar bv ->
      begin
        match find_exp bv.v with
          | Some e -> e
          | None ->
            let sort' = subst_typ' s bv.sort in
            Exp_bvar (setsort bv sort')
      end
    | _ -> e

let subst_kind s k = subst_kind' (mk_subst_map s) k 
let subst_typ s t = subst_typ' (mk_subst_map s) t
let subst_exp s e = subst_exp' (mk_subst_map s) e 

let open_typ typ (te:either<typ,exp>) : typ =
  match compress_typ typ, te with
    | Typ_fun(None, targ, tret, _), Inr _ -> tret
    | Typ_lam(bvd, targ, tret), Inr exp
    | Typ_fun(Some bvd, targ, tret, _), Inr exp -> subst_typ [Inr(bvd,exp)] tret
    | Typ_tlam(bvd, k, t), Inl targ
    | Typ_univ(bvd, k, t), Inl targ -> subst_typ [Inl(bvd, targ)] t
    | _ -> failwith "impossible"

let close_with_lam tps t = List.fold_right
  (fun tp out -> match tp with
    | Tparam_typ (a,k) -> Typ_tlam (a,k,out)
    | Tparam_term (x,t) -> Typ_lam (x,t,out))
  tps t 

let close_with_arrow tps t =
  t |> (tps |> List.fold_right (
    fun tp out -> match tp with
      | Tparam_typ (a,k) -> Typ_univ (a,k,out)
      | Tparam_term (x,t) -> Typ_fun (Some x,t,out,true)))

let close_typ = close_with_arrow
      
let close_kind tps k = 
    List.fold_right 
        (fun tp k -> match tp with
            | Tparam_typ (a, k') -> Kind_tcon(Some a, k', k, false)
            | Tparam_term (x, t) -> Kind_dcon(Some x, t, k, false))
        tps k 

let instantiate_tparams t tps (args:list<either<typ,exp>>) =
  List.fold_left open_typ (close_with_lam tps t) args

(********************************************************************************)
(******************************** Alpha conversion ******************************)
(********************************************************************************)
let ext subst = function
  | Inl btv ->
    let bvd' = new_bvd (Some btv.p) in
    let t = bvd_to_typ bvd' btv.sort in
    Inl (btv.v, t)::subst, Inl bvd'

  | Inr bxv ->
    let bvd' = new_bvd (Some bxv.p) in
    let e = bvd_to_exp bvd' bxv.sort in
    Inr (bxv.v, e)::subst, Inr bvd' 

let freshen_label ropt _ e = match ropt with
  | None -> e
  | Some r ->
    let rstr = Range.string_of_range r in
    match unascribe e with
      | Exp_constant(Const_string(bytes, p)) ->
        let bytes =  Util.unicode_of_string (Util.string_of_unicode bytes ^ " : " ^ rstr) in
        Exp_constant(Const_string(bytes, p))
      | _ -> e 

let freshen_bvars_typ (ropt:option<Range.range>) (t:typ) (subst:subst) : typ =
  snd (Visit.visit_typ
         fold_kind_noop
         (fun () subst t -> (), subst_tvar (mk_subst_map subst) t)
         (fun () subst e -> (), subst_xvar (mk_subst_map subst) e)
         (freshen_label ropt)
         ext () subst t) 

let freshen_bvars_kind (ropt:option<Range.range>) (k:kind) (subst:subst) : kind =
  snd (Visit.visit_kind
         fold_kind_noop
         (fun () subst t -> (), subst_tvar (mk_subst_map subst) t)
         (fun () subst e -> (), subst_xvar (mk_subst_map subst) e)
         (freshen_label ropt)
         ext () subst k)

(* move to de Bruijn? *)
let freshen_typ t benv   : typ  = freshen_bvars_typ None t benv
let alpha_convert t      : typ  = freshen_bvars_typ None t []
let alpha_convert_kind k : kind = freshen_bvars_kind None k []
let alpha_fresh_labels r t : typ = freshen_bvars_typ (Some r) t []


(********************************************************************************)
(******************** Reducing to weak head normal form *************************)
(***********************(inefficient--see Krivine.fs)****************************)

let whnf t =
  let rec aux ctr t =
    let t' = match compress_typ t with
      | Typ_dep(t1, e, imp) ->
        let t1,ctr = aux (ctr+1) t1 in
        (match t1 with
          | Typ_lam(x, t1_a, t1_r) ->
            let t1_r' = subst_typ [Inr(x,e)] t1_r in
            aux (ctr+1) t1_r'
          | _ -> Typ_dep(t1, e, imp), ctr)
      | Typ_app(t1, t2, imp) ->
        let t1,ctr = aux (ctr+1) t1 in
        let t2,ctr = aux (ctr+1) t2 in
        (match t1 with
          | Typ_tlam(a, t1_a, t1_r) ->
            let t1_r' = subst_typ [Inl(a,t2)] t1_r in
            aux (ctr+1) t1_r'
          | _ -> Typ_app(t1, t2, imp), ctr)
      | t -> t,ctr in
    t' in
  fst (aux 0 t)

(********************************************************************************)
(*********************** Various tests on constants  ****************************)
(********************************************************************************)

let is_lid_equality x =
  (lid_equals x Const.eq_lid) ||
    (lid_equals x Const.eq2_lid) ||
    (lid_equals x Const.eqA_lid) ||
    (lid_equals x Const.eqTyp_lid)

let is_forall lid = lid_equals lid Const.forall_lid
let is_exists lid = lid_equals lid Const.exists_lid
let is_qlid lid   = is_forall lid || is_exists lid
let is_equality x = is_lid_equality x.v

let lid_is_connective =
  let lst = [Const.and_lid; Const.or_lid; Const.not_lid;
             Const.iff_lid; Const.implies_lid] in
  fun lid -> Util.for_some (lid_equals lid) lst
    
let is_constructor t lid =
  match pre_typ t with
    | Typ_const tc -> lid_equals tc.v lid
    | _ -> false
      
let rec is_constructed_typ t lid = match pre_typ t with
  | Typ_const _ -> is_constructor t lid
  | Typ_app(t, _, _)
  | Typ_dep(t, _, _) -> is_constructed_typ t lid
  | _ -> false

let rec get_tycon t = 
  let t = pre_typ t in
  match t with
  | Typ_btvar _ 
  | Typ_const _  -> Some t
  | Typ_app(t, _, _)
  | Typ_dep(t, _, _) -> get_tycon t
  | _ -> None

let base_kind = function
  | Kind_star -> true
  | _ -> false

let sortByFieldName (fn_a_l:list<(fieldname * 'a)>) =
  fn_a_l |> List.sortWith
      (fun (fn1, _) (fn2, _) ->
        String.compare
          (text_of_lid fn1)
          (text_of_lid fn2))
    
let mk_tlam xopt t1 t2 = match xopt with
  | None ->  Typ_lam(new_bvd None, t1, t2)
  | Some x-> Typ_lam(x, t1, t2)

let mkRefinedUnit formula =
  let bvd = new_bvd None in
  let t = Typ_refine(bvd, ftv Const.unit_lid, formula) in
  t, bvd.realname

let findValDecl (vds:list<sigelt>) bvd : option<sigelt> =
  vds |> Util.find_opt (function
                         | Sig_val_decl(lid, t, _, _) -> lid.ident.idText = bvd.ppname.idText
                         | _ -> false)
      
//let findValDecls (vds:list<sigelt>) ((lb, _): (letbinding * bool)) : list<sigelt> =
//  lb |> List.choose (fun (lid', _, _) ->
//    Util.find_map vds (fun se -> match se with
//      | Sig_val_decl(lid, t) when lid_equals lid lid' -> Some se
//      | _ -> None))

let rec typs_of_letbinding x = match x with
  | (_, t, e)::tl -> t::typs_of_letbinding tl
  | _ -> []

let mk_conj phi1 phi2 = match phi1 with
  | None -> Some phi2
  | Some phi1 ->
    let app1 = Typ_app(ftv Const.and_lid, phi1, false) in
    let and_t = Typ_app(app1, phi2, false) in
    Some and_t

let normalizeRefinement t =
  let rec aux xopt t = match t with
    | Typ_refine(bvd, t', phi) ->
      let x, phi = match xopt with
        | None ->
          Some (bvd_to_exp bvd t'), phi
        | Some x ->
          xopt, subst_typ [Inr(bvd,x)] phi in
      let t', phi_opt = aux xopt t' in
      t', mk_conj phi_opt phi
    | _ -> t, None in
  aux None t

let forall_kind =
  let a = new_bvd None in
  let atyp = bvd_to_typ a Kind_star in
    Kind_tcon(Some a, Kind_star,
              Kind_tcon(None, Kind_dcon(None, atyp, Kind_star, false),
                        Kind_star, 
                        false), 
              true)

let mkForall (x:bvvdef) (a:typ) (body:typ) : typ =
  let forall_typ = Typ_const(withsort Const.forall_lid forall_kind) in
  Typ_app(Typ_app(forall_typ, a, true), Typ_lam(x, a, body), false)

let unForall t = match t.v with
  | Typ_app(Typ_app(Typ_const(lid), _, _), 
            Typ_lam(x, t, body), _) when is_forall lid.v ->
    Some (x, t, body)
  | _ -> None

let collect_formals t = 
  let rec aux out t =
    match whnf t with
      | Typ_fun(xopt, t1, t2, _) -> aux (Inr(xopt, t1)::out) t2
      | Typ_univ(a, k, t2) -> aux (Inl(a, k)::out) t2
      | Typ_meta(Meta_pos(t, _)) -> failwith "Unexpected position tagged type"
      | t -> List.rev out, t 
  in aux [] t
  
let collect_u_quants t =
  let rec aux out t =
    match flatten_typ_apps (whnf t) with
      | Typ_fun(Some x, t1, t2, _), _ -> aux ((x, t1)::out) t2
      | Typ_const tc, [Inl t1; Inl (Typ_lam(x, _, t2))]
        when is_forall tc.v ->
        aux ((x, t1)::out) t2
      | _ -> List.rev out, t
  in aux [] t

let collect_forall_xt t =
  let rec aux out t =
    match flatten_typ_apps (whnf t) with
      | Typ_fun(Some x, t1, t2, _), _ -> aux (Inr(x, t1)::out) t2
      | Typ_const tc, [Inl t1; Inl (Typ_lam(x, _, t2))]
        when is_forall tc.v ->
        aux (Inr(x, t1)::out) t2
      | Typ_univ(a, k, t), _ ->  aux (Inl(a,k)::out) t
      | _ -> List.rev out, t
  in aux [] t

let collect_exists_xt t =
  let rec aux out t =
      match flatten_typ_apps (whnf t) with
        | Typ_const tc, [Inl t1; Inl (Typ_lam(x, _, t2))]
          when lid_equals tc.v Const.exists_lid ->
          aux (Inr(x, t1)::out) t2
        | Typ_const tc, [Inl (Typ_tlam(a, k, t2))]
          when (lid_equals tc.v Const.exTyp_lid) ->
          aux (Inl(a,k)::out) t2
        | _ -> List.rev out, t
  in aux [] t
  
let collect_e_quants t =
  let rec aux out t =
      match flatten_typ_apps (whnf t) with
        | Typ_const tc, [Inl t1; Inl (Typ_lam(x, _, t2))]
          when lid_equals tc.v Const.exists_lid ->
          aux ((x, t1)::out) t2
        | _ -> List.rev out, t
  in aux [] t

//let check_bvar_identity t : bool =
//  let check_btv flag benv btv =
//    let f = function 
//      | Inr _ -> false 
//      | Inl btv' -> btv'.realname.idText = btv.realname.idText in
//      match Util.find_opt f benv with
//        | Some(Inl btv') ->
//            if not (Util.physical_eq btv.instantiation btv'.instantiation)
//            then (Util.print_string (Util.format1 "Btvar identity is broken for %s\n" btv.ppname.idText); false)
//            else flag
//        | _ -> Util.print_string (Util.format1 "Btvar is free %s\n" btv.ppname.idText); flag in
//  let check_bvv flag benv btv =
//    let f = function 
//      | Inl _ -> false 
//      | Inr btv' -> btv'.realname.idText = btv.realname.idText in
//      match Util.find_opt f benv with
//        | Some(Inr btv') ->
//            if not (Util.physical_eq btv.instantiation btv'.instantiation)
//            then (Util.print_string <| Util.format1 "Bvar identity is broken for %s\n" btv.ppname.idText; false)
//            else flag
//        | _ -> Util.print_string <| Util.format1 "Bvar is free %s\n" btv.ppname.idText; flag in
//  let fold_t flag benv t = match t with
//    | Typ_btvar bv -> check_btv flag benv bv.v, t
//    | _ -> flag, t in
//  let fold_e flag benv e = match e with
//    | Exp_bvar bv -> check_bvv flag benv bv.v, e
//    | _ -> flag, e in
//  let ext benv = function
//    | Inl btv ->
//        (Inl btv.v)::benv, Inl btv.v
//    | Inr bxv ->
//        (Inr bxv.v)::benv, Inr bxv.v in
//    fst (Visit.visit_typ fold_kind_noop fold_t fold_e (fun _ e -> e) ext true [] t)

let rec check_pat_vars r = function 
  | Pat_cons(_, ps) -> 
    let vars = List.collect (check_pat_vars r) ps in 
    if vars |> nodups (fun x y -> match x, y with 
      | Inl x, Inl y -> bvd_eq x y
      | Inr x, Inr y -> bvd_eq x y
      | _ -> false) 
    then vars
    else raise (Error("Pattern variables may not occur more than once", r))
  | Pat_var x -> [Inr x]
  | Pat_tvar a -> [Inl a]
  | Pat_disj ps -> 
    let vars = List.map (check_pat_vars r) ps in 
    if not (List.tl vars |> Util.for_all (Util.set_eq order_bvd (List.hd vars)))
    then 
      let vars = Util.concat_l ";\n" (vars |> 
          List.map (fun v -> Util.concat_l ", " (List.map (function 
            | Inr x -> x.ppname.idText 
            | Inl x -> x.ppname.idText) v))) in
      raise (Error(Util.format1 "Each branch of this pattern binds different variables: %s" vars, r))
    else List.hd vars
  | Pat_wild 
  | Pat_twild
  | Pat_constant _ -> []
  | Pat_withinfo (p, r) -> check_pat_vars r p
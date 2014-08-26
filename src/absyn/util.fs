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
        Util.print_string (Util.format3 "%s : %s\n%s\n" (Range.string_of_range r) (if warning then "Warning" else "Error") msg);
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

//let compress_kind = Visit.compress_kind
//let compress_typ  = Visit.compress_typ
//let compress_exp  = Visit.compress_exp 
let compress_comp = Visit.compress_comp

(********************************************************************************)
(**************************Utilities for identifiers ****************************)
(********************************************************************************)

let gensym = 
  let ctr = mk_ref 0 in 
  (fun () -> Util.format1 "_%s" (Util.string_of_int (incr ctr; !ctr)))
    
let rec gensyms x = match x with
  | 0 -> []
  | n -> gensym ()::gensyms (n-1)
    
let genident r = 
  let sym = gensym () in
  match r with 
    | None -> mk_ident(sym, dummyRange)
    | Some r -> mk_ident(sym, r)

let bvd_eq bvd1 bvd2 = bvd1.realname.idText=bvd2.realname.idText
let range_of_bvd x = x.ppname.idRange
let mkbvd (x,y) = {ppname=x;realname=y}
let setsort w t = {v=w.v; sort=t; p=w.p}
let withinfo e s r = {v=e; sort=s; p=r}
let withsort e s   = withinfo e s dummyRange
let bvar_ppname bv = bv.v.ppname 
let bvar_realname bv = bv.v.realname
let bvar_eq (bv1:bvar<'a,'b>) (bv2:bvar<'a,'b>) = bvd_eq bv1.v bv2.v
let lbname_eq l1 l2 = match l1, l2 with
  | Inl x, Inl y -> bvd_eq x y
  | Inr l, Inr m -> lid_equals l m
  | _ -> false
let fvar_eq fv1 fv2  = lid_equals fv1.v fv2.v
let bvd_to_bvar_s bvd sort = {v=bvd; sort=sort; p=bvd.ppname.idRange}
let bvar_to_bvd bv = bv.v
let btvar_to_typ bv  = mk_Typ_btvar bv bv.sort bv.p
let bvd_to_typ bvd k = btvar_to_typ (bvd_to_bvar_s bvd k)
let bvar_to_exp bv   =  mk_Exp_bvar bv bv.sort bv.p
let bvd_to_exp bvd t = bvar_to_exp (bvd_to_bvar_s bvd t)
let new_bvd ropt = let id = genident ropt in mkbvd (id,id)
let freshen_bvd bvd' = mkbvd(bvd'.ppname, genident (Some <| range_of_bvd bvd'))
let gen_bvar sort = let bvd = (new_bvd None) in bvd_to_bvar_s bvd sort
let gen_bvar_p r sort = let bvd = (new_bvd (Some r)) in bvd_to_bvar_s bvd sort
let bvdef_of_str s = let id = id_of_text s in mkbvd(id, id)
let set_bvd_range bvd r = {ppname=mk_ident(bvd.ppname.idText, r);
                           realname=mk_ident(bvd.realname.idText, r)}
let set_lid_range l r = 
  let ids = (l.ns@[l.ident]) |> List.map (fun i -> mk_ident(i.idText, r)) in
  lid_of_ids ids
let fv l = withinfo l tun (range_of_lid l)
let fvar l r = mk_Exp_fvar(fv (set_lid_range l r), false) tun r
let ftv l k = mk_Typ_const (withinfo l k (range_of_lid l)) k (range_of_lid l)
let order_bvd x y = match x, y with 
  | Inl _, Inr _ -> -1
  | Inr _, Inl _ -> 1
  | Inl x, Inl y -> String.compare x.ppname.idText y.ppname.idText
  | Inr x, Inr y -> String.compare x.ppname.idText y.ppname.idText

(********************************************************************************)
(*************************** Delayed substitutions ******************************)
(********************************************************************************)
let subst_to_string s = 
  s |> List.map (function Inl (b, _) -> b.realname.idText | Inr (x, _) -> x.realname.idText) |> String.concat ", "

(* delayed substitutions *)
let subst_tvar s t = match t.n with 
  | Typ_btvar a -> 
    begin match Util.find_opt (function Inl (b, _) -> bvd_eq b a.v | _ -> false) s.subst with 
      | Some (Inl(_, t)) -> t
      | _ -> t
    end
  | _ -> failwith "impossible"
let subst_xvar s e = match e.n with
  | Exp_bvar x -> 
    begin match Util.find_opt (function Inr(y, _) -> bvd_eq y x.v | _ -> false) s.subst with
            | Some (Inr(_, e)) -> e
            | _ -> e
    end
  | _ -> failwith "impossible"
let rec subst_typ s t = match s.subst with 
  | [] -> t
  | _ -> 
    let t0 = Visit.compress_typ t in
    match t0.n with 
    | Typ_delayed(t', s', m) -> mk_Typ_delayed (t', compose_subst s' s, Util.mk_ref None) t.tk t.pos
    | Typ_btvar a -> subst_tvar s t0
    | _ -> mk_Typ_delayed(t, s, Util.mk_ref None) t.tk t.pos

and subst_exp s e = match s.subst with 
  | [] -> e
  | _ -> 
    let e0 = Visit.compress_exp e in
    match e0.n with
    | Exp_delayed(e, s',m) -> mk_Exp_delayed (e, compose_subst s' s, Util.mk_ref None) e.tk e.pos
    | Exp_bvar _ -> subst_xvar s e0
    | _ -> mk_Exp_delayed (e0, s, Util.mk_ref None) e0.tk e0.pos

and subst_kind s k = match s.subst with 
  | [] -> k 
  | _ -> 
  let k0 = Visit.compress_kind k in
    match k0.n with
    | Kind_type
    | Kind_effect
    | Kind_unknown -> k0
    | Kind_delayed(k, s',m) -> mk_Kind_delayed(k, compose_subst s' s, Util.mk_ref None) k0.pos
    | _ -> mk_Kind_delayed(k0, s, Util.mk_ref None) k0.pos

and subst_comp_typ s t = match s.subst with 
  | [] -> t
  | _ -> 
    {t with result_typ=subst_typ s t.result_typ; 
            effect_args=List.map (function Inl t -> Inl <| subst_typ s t | Inr e -> Inr <| subst_exp s e) t.effect_args}
and subst_comp s t = match s.subst with 
  | [] -> t
  | _ -> 
    let t0 = compress_comp t in
    match t0.n with 
      | Total t -> mk_Total (subst_typ s t)
      | Rigid t -> mk_Rigid (subst_typ s t)
      | Flex(u, t) -> mk_Flex(u, subst_typ s t)
      | Comp ct -> mk_Comp(subst_comp_typ s ct)

and compose_subst (s1:subst) (s2:subst) = 
  mk_subst <| ((s1.subst |> List.map (function 
      | Inl(x, t) -> Inl (x, subst_typ s2 t)
      | Inr(x, e) -> Inr (x, subst_exp s2 e)))@s2.subst)

let subst_kind' s t = subst_kind (mk_subst s) t
let subst_typ' s t = subst_typ (mk_subst s) t
let subst_exp' s t = subst_exp (mk_subst s) t
let subst_comp' s t = subst_comp (mk_subst s) t

let restrict_subst axs s = 
  s.subst |> List.filter (fun b ->
    let r = match b with 
    | Inl(a, _) -> not (axs |> Util.for_some (function Inr _ -> false | Inl b -> bvd_eq a b))
    | Inr(x, _) -> not (axs |> Util.for_some (function Inl _ -> false | Inr y -> bvd_eq x y)) in
    //if not r then printfn "Filtering %s\n" (match b with Inl (b, _) -> b.realname.idText | Inr (x, _) -> x.realname.idText);
    r) |> mk_subst

type red_ctrl = {
    stop_if_empty_subst:bool;
    descend:bool
}
let alpha_ctrl = {stop_if_empty_subst=false; descend=true} 
let subst_ctrl = {stop_if_empty_subst=true; descend=true} 
let null_ctrl = {stop_if_empty_subst=true; descend=false} 
 

let rec map_knd s vk mt me descend binders k = 
  subst_kind (restrict_subst binders s) k, descend
and map_typ s mk vt me descend binders t = 
  subst_typ (restrict_subst binders s) t, descend
and map_exp s mk me ve descend binders e =
  subst_exp (restrict_subst binders s) e, descend
and map_comp s mk map_typ map_exp descend binders c = match (Visit.compress_comp c).n with 
    | Flex (u, t) -> 
      let u, descend = map_typ descend binders u in 
      let t, descend = map_typ descend binders t in
      mk_Flex(u, t), descend    
    | Rigid t -> 
      let t, descend = map_typ descend binders t in
      mk_Rigid(t), descend    
    | Total t -> 
      let t, descend = map_typ descend binders t in
      mk_Total t, descend
    | Comp ct ->
      let t, descend = map_typ descend binders ct.result_typ in
      let descend, args = List.fold_left (fun (desc, out) -> function
        | Inl t -> 
          let t, desc = map_typ desc binders t in
          desc, Inl t::out
        | Inr e -> 
          let e, desc = map_exp desc binders e in
          desc, Inr e::out) (descend, []) ct.effect_args in 
      mk_Comp ({ct with result_typ=t; effect_args=List.rev args}), descend 
and visit_knd s vk mt me ctrl binders k = 
  let k = Visit.compress_kind k in 
  if ctrl.descend 
  then let k, _ = vk null_ctrl binders k in k, ctrl
  else map_knd s vk mt me null_ctrl binders k
and visit_typ s mk vt me ctrl binders t = 
  let visit_prod ax tc = 
    let ax, s, binders = match ax with 
    | Inl(a, k) -> 
      //printfn "Visit prod for %s" (a.ppname.idText ^ a.realname.idText);
      let k, _ = map_knd s mk vt me null_ctrl binders k in
      let binders' = Inl a::binders in
      let s = restrict_subst binders' s in
      (match s.subst with 
        | [] when ctrl.stop_if_empty_subst -> Inl(a,k), s, binders'
        | _ -> 
            let b = freshen_bvd a in
            let s = extend_subst (Inl(a, bvd_to_typ b k)) s in
            Inl(b,k), s, Inl b::binders)
    | Inr(x, t1) -> 
      let t1, _ = map_typ s mk vt me null_ctrl binders t1 in
      let binders' = Inr x::binders in
      let s = restrict_subst binders' s in 
      (match s.subst with
        | [] when ctrl.stop_if_empty_subst -> Inr(x,t1), s, binders
        | _ -> 
           let y = freshen_bvd x in
           let s = extend_subst (Inr(x, bvd_to_exp y t1)) s in
           Inr(y,t1), s, Inr y::binders) in
     let tc = match s.subst, tc with 
        | [], _ -> tc
        | _, Inl t -> Inl (fst <| map_typ s mk vt me null_ctrl binders t)
        | _, Inr c -> Inr (fst <| map_comp s mk (map_typ s mk vt me) (map_exp s mk vt me) null_ctrl binders c) in
     ax, tc  in

  let t0 = t in
  match t0.n with
    | Typ_btvar a -> 
      //printfn "Trying to subst. %s with [%s]\n" (a.v.realname.idText) (s |> subst_to_string);
      compress_typ <| subst_tvar (restrict_subst binders s) t, ctrl
    
    | _ when (not ctrl.descend) -> map_typ s mk vt me null_ctrl binders t

     (* all the binding forms need to be alpha-converted to avoid capture *)
    | Typ_fun(Some x, t, c, b) ->
        (match visit_prod (Inr(x,t)) (Inr c) with 
            | Inr(y,t), Inr c -> mk_Typ_fun (Some y, t, c, b) t0.tk t0.pos, ctrl
            | _ -> failwith "Impossible")

    | Typ_univ(a, k, c) -> 
         (match visit_prod (Inl(a,k)) (Inr c) with 
            | Inl(a,k), Inr c -> mk_Typ_univ(a, k, c) t0.tk t0.pos, ctrl
            | _ -> failwith "Impossible")

    | Typ_refine(x, t1, t2) -> 
        (match visit_prod (Inr(x,t1)) (Inl t2) with 
            | Inr(x,t1), Inl t2 -> mk_Typ_refine(x, t1, t2) t0.tk t0.pos, ctrl
            | _ -> failwith "Impossible")
    
    | Typ_lam(x, t1, t2) -> 
        (match visit_prod (Inr(x,t1)) (Inl t2) with 
            | Inr(x,t1), Inl t2 -> mk_Typ_lam(x, t1, t2) t0.tk t0.pos, ctrl
            | _ -> failwith "Impossible")
    
    | Typ_tlam(a, k, t2) -> 
        (match visit_prod (Inl(a,k)) (Inl t2) with 
            | Inl(a,k), Inl t2 -> mk_Typ_tlam(a, k, t2) t0.tk t0.pos, ctrl
            | _ -> failwith "Impossible")
    
    | _ -> let t, _ = vt null_ctrl binders t in t, ctrl
and visit_exp s mk me ve ctrl binders e =
  let e = Visit.compress_exp e in 
  match e.n with 
    | Exp_bvar _ -> compress_exp <| subst_xvar (restrict_subst binders s) e, ctrl
    | _ when (not ctrl.descend) -> map_exp s mk me ve ctrl binders e
    | _ -> let e, _ = ve null_ctrl binders e in e, ctrl

and compress_kind k = 
  let k = Visit.compress_kind k in
  match k.n with 
  | Kind_delayed (k',s, m) ->
    let k' = fst <| Visit.reduce_kind (visit_knd s) (map_typ s) (map_exp s) Visit.combine_kind Visit.combine_typ Visit.combine_exp subst_ctrl [] k' in
    m := Some k'; 
    k'
  | _ -> k
and compress_typ t = 
  let t = Visit.compress_typ t in
  match t.n with
  | Typ_delayed (t', s, m) ->
    let res = fst <| Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) Visit.combine_kind Visit.combine_typ Visit.combine_exp subst_ctrl [] t' in
    m := Some res;
    //printfn "Compressing %A ... got %A\n" t' res;
    res
  | _ -> t
and compress_exp e = 
  let e = Visit.compress_exp e in
  match e.n with
  | Exp_delayed (e',s, m) ->
    let e = fst <| Visit.reduce_exp (map_knd s) (map_typ s) (visit_exp s) Visit.combine_kind Visit.combine_typ Visit.combine_exp subst_ctrl [] e' in
    m := Some e;
    e
  | _ -> e
  
let alpha_typ t = 
   let t = compress_typ t in
   let s = mk_subst [] in
   match t.n with 
    | Typ_lam _
    | Typ_tlam _
    | Typ_refine _ 
    | Typ_fun _ 
    | Typ_univ _ -> fst <| Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) Visit.combine_kind Visit.combine_typ Visit.combine_exp alpha_ctrl [] t 
    | _ -> t
    
let compress_typ_opt = function
    | None -> None
    | Some t -> Some (compress_typ t)

let mk_discriminator lid = 
  lid_of_ids (lid.ns@[Syntax.mk_ident("is_" ^ lid.ident.idText, lid.ident.idRange)])

let is_name (lid:lident) = 
  let c = Util.char_at lid.ident.idText 0 in
  Util.is_upper c


let ml_comp t r =  
  mk_Comp ({effect_name=set_lid_range Const.ml_effect_lid r;
         result_typ=t;
         effect_args=[];
         flags=[MLEFFECT]})
    
let total_comp t r = mk_Total t

let comp_flags c = match (compress_comp c).n with 
  | Total _ -> [TOTAL]
  | Comp ct -> ct.flags
  | Flex _ -> []
  | Rigid _ -> failwith "Normalize comp types before calling this function"

let is_total_comp c = comp_flags c |> Util.for_some (function TOTAL | RETURN -> true | _ -> false)

let is_pure_comp c = match (compress_comp c).n with 
    | Total _ -> true
    | Comp ct -> is_total_comp c || Util.starts_with ct.effect_name.str "Prims.PURE"
    | Flex _ -> false
    | Rigid _ -> failwith "Normalize comp types before calling this function"

let is_ml_comp c = match c.n with
  | Comp c -> lid_equals c.effect_name Const.ml_effect_lid || List.contains MLEFFECT c.flags
  | _ -> false

let comp_result c = match (compress_comp c).n with 
  | Total t
  | Flex (_, t) -> t
  | Comp ct -> ct.result_typ
  | Rigid _ -> failwith "Normalize comp types before calling this function"

let set_result_typ c t = match (compress_comp c).n with 
  | Total _ -> mk_Total t
  | Flex(u, _) -> mk_Flex(u, t)
  | Comp ct -> mk_Comp({ct with result_typ=t})
  | Rigid _ -> failwith "Normalize comp types before calling this function"

let is_trivial_wp c = 
  comp_flags c |> Util.for_some (function TOTAL | RETURN -> true | _ -> false)
  
(********************************************************************************)
(****************Simple utils on the local structure of a term ******************)
(********************************************************************************)
let primops = 
  [Const.op_Eq;
   Const.op_notEq;
   Const.op_LT;
   Const.op_LTE;
   Const.op_GT;
   Const.op_GTE;
   Const.op_Subtraction;
   Const.op_Minus;
   Const.op_Addition;
   Const.op_Multiply;
   Const.op_Division;
   Const.op_Modulus;
   Const.op_And;
   Const.op_Or;
   Const.op_Negation;]

let is_primop f = match f.n with 
  | Exp_fvar(fv,_) -> primops |> Util.for_some (lid_equals fv.v)
  | _ -> false

let rec ascribe e t = match e.n with 
  | Exp_ascribed (e, _) -> ascribe e t
  | _ -> mk_Exp_ascribed(e, t) e.pos
    
let rec unascribe e = match e.n with 
  | Exp_ascribed (e, _) -> unascribe e 
  | _ -> e

let rec ascribe_typ t k = match t.n with 
  |  Typ_ascribed (t', _) -> ascribe_typ t' k
  | _ -> mk_Typ_ascribed(t, k) t.pos
     
let rec unascribe_typ t = match t.n with 
  | Typ_ascribed (t, _) -> unascribe_typ t
  | _ -> t

let rec unrefine t = match t.n with 
  | Typ_refine(x, t, _) -> unrefine t
  | _ -> t

let is_fun e = match (compress_exp e).n with 
  | Exp_abs _
  | Exp_tabs _ -> true
  | _ -> false

let rec pre_typ t = 
    let t = compress_typ t in 
    match t.n with 
      | Typ_refine(_, t, _) 
      | Typ_ascribed(t, _) -> pre_typ t
      | _ -> t

(* If the input type is a Typ_app, walks the Typ_app tree and
   flattens the type parameters. Does not recursively drill into
   other kinds of types. *)
let flatten_typ_apps : typ -> typ * (list<either<typ,exp>>) =
  let rec aux acc t = 
    let t = pre_typ t in
    match t.n with
      | Typ_app(t1, t2, _) -> aux (Inl t2::acc) t1 
      | Typ_dep(t1, v, _) -> aux (Inr v::acc) t1
      | _              -> t, acc in
  (fun t -> aux [] t)

let flatten_exp_apps (e:exp) : exp * (list<either<typ, exp>>) = 
  let rec aux e out = match (compress_exp e).n with 
    | Exp_app(e1, e2, _) -> aux e1 (Inr e2::out)
    | Exp_tapp(e1, t) -> aux e1 (Inl t::out)
    | Exp_ascribed(e, _) -> aux e out
    | _ -> e, out in
  aux e []

let destruct typ lid = 
  match flatten_typ_apps typ with 
    | {n=Typ_const tc}, args when lid_equals tc.v lid -> Some args
    | _ -> None

let rec lids_of_sigelt se = match se with 
  | Sig_bundle(ses, _) -> List.collect lids_of_sigelt ses
  | Sig_tycon (lid, _, _,  _, _, _, _)    
  | Sig_typ_abbrev  (lid, _, _, _, _, _)
  | Sig_datacon (lid, _, _, _, _)
  | Sig_val_decl (lid, _, _, _) 
  | Sig_assume (lid, _, _, _) -> [lid]
  | Sig_let((_, lbs), _) -> List.map (function 
    | (Inr l, _, _) -> l
    | (Inl x, _, _) -> failwith (Util.format1 "Impossible: got top-level letbinding with name %s" x.ppname.idText)) lbs
  | Sig_main _ -> []
  | Sig_monads(mdecls, _, _) -> mdecls |> List.map (fun md -> md.mname)
    
let lid_of_sigelt se : option<lident> = match lids_of_sigelt se with
  | [l] -> Some l
  | _ -> None
let range_of_sigelt x = match x with 
  | Sig_bundle(_, r) 
  | Sig_tycon (_, _, _,  _, _, _, r)    
  | Sig_typ_abbrev  (_, _, _, _, _, r)
  | Sig_datacon (_, _, _, _, r)
  | Sig_val_decl (_, _, _, r) 
  | Sig_assume (_, _, _, r)
  | Sig_let(_, r) 
  | Sig_main(_, r) 
  | Sig_monads(_, _, r) -> r

let range_of_lb = function
  | (Inl x, _, _) -> range_of_bvd x
  | (Inr l, _, _) -> range_of_lid l 

let mk_curried_app e e_or_t = 
  List.fold_left (fun f -> function
    | Inl t -> mk_Exp_tapp(f, t) tun (Range.union_ranges f.pos t.pos)
    | Inr (e, imp) -> mk_Exp_app(f, e, imp) tun (Range.union_ranges f.pos e.pos))  e e_or_t 

let app_kind k te = match k.n, te with 
    | Kind_tcon(None, _, k', _), Inl t ->  k'
    | Kind_dcon(None, _, k', _), Inr e -> k'
    | Kind_tcon(Some a, _, k', _), Inl t -> subst_kind (mk_subst [(Inl(a, t))]) k'
    | Kind_dcon(Some x, _, k', _), Inr e -> subst_kind (mk_subst [(Inr(x, e))]) k'
    | _ -> kun

let app_typ t te = match t.n, te with 
    | Typ_fun(None, _, c, _), Inr _  -> comp_result c
    | Typ_fun(Some x, _, c, _), Inr e -> subst_typ (mk_subst [Inr(x, e)]) <| comp_result c
    | Typ_univ(a, _, c), Inl t -> subst_typ (mk_subst [Inl(a, t)]) <| comp_result c 
    | _ -> tun

let mk_typ_app f args = 
  List.fold_left (fun f -> function
    | Inl (t, imp) -> mk_Typ_app(f, t, imp) (app_kind f.tk (Inl t)) (Range.union_ranges f.pos t.pos)
    | Inr (e, imp) -> mk_Typ_dep(f, e, imp) (app_kind f.tk (Inr e)) (Range.union_ranges f.pos e.pos)) f args

let mk_typ_app_explicit f args = 
  List.fold_left (fun f -> function
    | Inl (t) -> mk_Typ_app(f, t, false) (app_kind f.tk (Inl t)) (Range.union_ranges f.pos t.pos)
    | Inr (e) -> mk_Typ_dep(f, e, false) (app_kind f.tk (Inr e)) (Range.union_ranges f.pos e.pos)) f args

let mk_exp_app_explicit f args = 
  List.fold_left (fun f -> function
    | Inl (t) -> mk_Exp_tapp(f, t) (app_typ f.tk (Inl t)) (Range.union_ranges f.pos t.pos)
    | Inr (e) -> mk_Exp_app(f, e, false) (app_typ f.tk (Inr e)) (Range.union_ranges f.pos e.pos)) f args

let uncurry_app e =
  let rec aux e out = match e.n with 
    | Exp_uvar(u, _) -> 
      begin match Unionfind.find u with 
        | Fixed e -> aux e out
        | _ -> e, out
      end
    | Exp_app(e1, e2, imp) -> aux e1 (Inr (e2, imp)::out)
    | Exp_tapp(e1, t) -> aux e1 (Inl t::out)
    | _ -> e, out in
  aux e []

let mk_data l args = 
  mk_Exp_meta(Meta_desugared(mk_curried_app (fvar l (range_of_lid l)) args, Data_app))

let destruct_app =
    let rec destruct acc (e : exp) =
        match e.n with
        | Exp_app (e1, e2, b) -> destruct ((e2, b) :: acc) e1
        | Exp_ascribed (e, _) -> destruct acc e
        | _ -> (e, acc)
    in

    fun e -> destruct [] e

let destruct_fun =
    let rec destruct acc (e : exp) =
        match e.n with
        | Exp_abs (x, ty, e) -> destruct ((x, ty) :: acc) e
        | Exp_ascribed (e, _) -> destruct acc e
        | _ -> (List.rev acc, e)
    in

    fun e -> destruct [] e

let unchecked_unify uv t = 
  match Unionfind.find uv with 
    | Fixed _ -> failwith "Changing a fixed uvar!"
    | _ -> Unionfind.change uv (Fixed t) (* used to be an alpha-convert t here *)

let as_comp = function 
   | {n=Typ_meta(Meta_comp c)} -> c
   | _ -> failwith "Impossible"

let destruct_flex_arg = function 
    | {n=Typ_meta(Meta_uvar_t_app(t, uv))} -> t, uv
    | _ -> failwith "Impossible"

(********************************************************************************)
(************************* Free type/term/unif variables ************************)
(********************************************************************************)
type freevars' = list<btvar> * list<bvvar>
let eq_fvars v1 v2 = match v1, v2 with 
    | Inl a, Inl b -> Syntax.bvd_eq a b
    | Inr x, Inr y -> Syntax.bvd_eq x y
    | _ -> false

let uv_eq (uv1,_) (uv2,_) = Unionfind.equivalent uv1 uv2
let union_uvs uvs1 uvs2 =
    {   uvars_k=Util.set_union uvs1.uvars_k uvs2.uvars_k;
        uvars_c=Util.set_union uvs1.uvars_c uvs2.uvars_c;
        uvars_t=Util.set_union uvs1.uvars_t uvs2.uvars_t;
        uvars_e=Util.set_union uvs1.uvars_e uvs2.uvars_e;
    }

let union_fvs (fvs1, uvs1) (fvs2, uvs2) = 
    {
        ftvs=Util.set_union fvs1.ftvs fvs2.ftvs;
        fxvs=Util.set_union fvs1.fxvs fvs2.fxvs;
    }, 
    union_uvs uvs1 uvs2

let sub_fv (fvs, uvs) (by:option<either<btvdef,bvvdef>>) = match by with 
    | None -> fvs, uvs
    | Some (Inl b) -> 
        {fvs with ftvs=Util.set_remove (bvd_to_bvar_s b kun) fvs.ftvs}, uvs
    | Some (Inr y) -> 
        {fvs with fxvs=Util.set_remove (bvd_to_bvar_s y tun) fvs.fxvs}, uvs
    //    {fvs with fxvs=fvs.fxvs |> List.filter (fun a -> not <| bvd_eq a.v y)}, uvs

let tbinder = function 
    | None -> None
    | Some x -> Some <| Inl x
let vbinder = function 
    | None -> None
    | Some x -> Some <| Inr x


let stash (uvonly:bool) (s:syntax<'a,'b>) ((fvs:freevars), (uvs:uvars)) = 
    s.uvs := Some uvs;
    if uvonly then ()
    else s.fvs := Some fvs

let single_fv x = Util.set_add x (new_ftv_set())
let single_uv u = Util.set_add u (new_uv_set())
let single_uvt u = Util.set_add u (new_uvt_set())

let rec vs_typ' (t:typ) (uvonly:bool) (cont:(freevars * uvars) -> 'res) : 'res =
    let t = compress_typ t in
    match t.n with
        | Typ_delayed _ -> failwith "Impossible"
        | Typ_btvar a -> 
          if uvonly 
          then cont (no_fvs, no_uvs)
          else cont ({no_fvs with ftvs=single_fv a}, no_uvs)

        | Typ_uvar (uv, k) -> cont (no_fvs, {no_uvs with uvars_t=single_uvt (uv,k)})

        | Typ_unknown        
        | Typ_const _ -> cont (no_fvs, no_uvs)

        | Typ_fun(xopt, t, c, _) -> 
          vs_typ t uvonly (fun ft1 -> 
          vs_comp c uvonly (fun ft2 -> 
          let fvs = union_fvs ft1 (sub_fv ft2 (vbinder xopt)) in
          cont fvs)) 

        | Typ_refine(x, t1, t2)
        | Typ_lam(x, t1, t2) -> 
          vs_prod_tt uvonly (Some <| Inr x) t1 t2 cont

        | Typ_app(t1, t2, _) ->
          vs_prod_tt uvonly None t1 t2 cont

        | Typ_univ(a, k, c) -> 
          vs_kind k uvonly (fun ft1 -> 
          vs_comp c uvonly (fun ft2 -> 
          let fvs = union_fvs ft1 (sub_fv ft2 (Some <| Inl a)) in
          cont fvs)) 
    
        | Typ_tlam(a, k, t) -> 
          vs_kind k uvonly (fun ft1 -> 
          vs_typ t uvonly (fun ft2 -> 
          let fvs = union_fvs ft1 (sub_fv ft2 (Some <| Inl a)) in
          cont fvs)) 
          
        | Typ_dep(t1, e1, _) ->
          vs_prod_te uvonly None t1 e1 cont
          
        | Typ_ascribed(t, _) -> 
          vs_typ t uvonly cont        

        | Typ_meta(Meta_uvar_t_app(t, (u,k))) -> 
          if uvonly 
          then cont (no_fvs, {no_uvs with uvars_t=single_uvt (u,k)})
          else vs_typ t uvonly cont

        | Typ_meta(Meta_named(t, _))
        | Typ_meta(Meta_pattern(t, _)) -> 
          vs_typ t uvonly cont

        | Typ_meta(Meta_comp c) -> 
          vs_comp c uvonly cont

and vs_typ (t:typ) (uvonly:bool) (cont:(freevars * uvars) -> 'res) : 'res = 
    match !t.fvs, !t.uvs with 
        | Some _, None -> failwith "Impossible"
        | None, None -> vs_typ' t uvonly (fun fvs -> stash uvonly t fvs; cont fvs)
        | None, Some uvs -> 
            if uvonly
            then cont (no_fvs, uvs)
            else vs_typ' t uvonly (fun fvs -> stash uvonly t fvs; cont fvs)
        | Some fvs, Some uvs -> cont (fvs, uvs)

and vs_prod_te (uvonly:bool) (x:option<either<btvdef,bvvdef>>) (t:typ) (e:exp) (k:(freevars * uvars) -> 'res) : 'res = 
    vs_typ t uvonly (fun ft1 -> 
    vs_exp e uvonly (fun ft2 -> 
    let fvs = union_fvs ft1 (sub_fv ft2 x) in
    k fvs)) 

and vs_prod_tt (uvonly:bool) (x:option<either<btvdef, bvvdef>>) (t1:typ) (t2:typ) (k:(freevars * uvars) -> 'res) : 'res = 
    vs_typ t1 uvonly (fun ft1 -> 
    vs_typ t2 uvonly (fun ft2 -> 
    let fvs = union_fvs ft1 (sub_fv ft2 x) in
    k fvs)) 
 
and vs_kind' (k:knd) (uvonly:bool) (cont:(freevars * uvars) -> 'res) : 'res = 
    let k = compress_kind k in 
    match k.n with 
        | Kind_delayed _ -> failwith "Impossible"
        | Kind_unknown
        | Kind_type
        | Kind_effect -> cont (no_fvs, no_uvs)

        | Kind_uvar (uv,vars) -> 
          let uvs = {no_uvs with uvars_k=single_uv uv} in
          let mk_freevars vars =
            List.fold_left (fun fvs -> function 
                | Inl a -> {fvs with ftvs=Util.set_add a fvs.ftvs}
                | Inr x -> {fvs with fxvs=Util.set_add x fvs.fxvs}) no_fvs vars in
          if uvonly 
          then cont (no_fvs, uvs)
          else cont (mk_freevars vars, uvs)
        
        | Kind_abbrev(_, k) -> 
          vs_kind k uvonly cont

        | Kind_dcon(aopt, t, k, _) -> 
          vs_typ t uvonly (fun ft1 -> 
          vs_kind k uvonly (fun ft2 -> 
          cont (union_fvs ft1 (sub_fv ft2 (vbinder aopt)))))

        | Kind_tcon(aopt, k1, k2, _) -> 
          vs_kind k1 uvonly (fun ft1 -> 
          vs_kind k2 uvonly (fun ft2 -> 
          cont (union_fvs ft1 (sub_fv ft2 (tbinder aopt)))))

and vs_kind (k:knd) (uvonly:bool) (cont:(freevars * uvars) -> 'res) : 'res =
    match !k.fvs, !k.uvs with 
        | Some _, None -> failwith "Impossible"
        | None, None -> 
          vs_kind' k uvonly (fun fvs -> stash uvonly k fvs; cont fvs)
        | None, Some uvs -> 
          if uvonly 
          then cont (no_fvs, uvs)
          else vs_kind' k uvonly (fun fvs -> stash uvonly k fvs; cont fvs)
        | Some fvs, Some uvs -> cont (fvs, uvs)
       
and vs_exp' (e:exp) (uvonly:bool) (cont:(freevars * uvars) -> 'res) : 'res = 
    let e = compress_exp e in 
    match e.n with
      | Exp_delayed _ -> failwith "impossible"
      | Exp_fvar _ 
      | Exp_constant _ -> cont (no_fvs, no_uvs) 

      | Exp_uvar (uv,t) -> cont (no_fvs, {no_uvs with uvars_e=single_uvt (uv,t)})
          
      | Exp_bvar x -> 
        if uvonly 
        then cont (no_fvs, no_uvs)
        else cont ({no_fvs with fxvs=single_fv x}, no_uvs)

      | Exp_ascribed(e, _) -> 
        vs_exp e uvonly cont
    
      | Exp_abs(x, t, e) -> 
        vs_prod_te uvonly (Some <| Inr x) t e cont
    
      | Exp_tabs(a, k, e) -> 
        vs_kind k uvonly (fun ft1 -> 
        vs_exp e uvonly (fun ft2 -> 
        cont (union_fvs ft1 (sub_fv ft2 (Some <| Inl a)))))
      
      | Exp_app(e1, e2, _) ->
        vs_exp e1 uvonly (fun ft1 -> 
        vs_exp e2 uvonly (fun ft2 -> 
        cont (union_fvs ft1 ft2)))

      | Exp_tapp(e, t) -> 
        vs_exp e uvonly (fun ft1 -> 
        vs_typ t uvonly (fun ft2 -> 
        cont (union_fvs ft1 ft2)))

      | Exp_match _       
      | Exp_let _ -> cont (no_fvs, no_uvs) //failwith "NYI"
                               
      | Exp_meta(Meta_desugared(e, _))
      | Exp_meta(Meta_datainst(e, _)) -> 
        vs_exp e uvonly cont

      | Exp_meta(Meta_uvar_e_app(e, (uv, t))) -> 
        if uvonly 
        then cont (no_fvs, {no_uvs with uvars_e=single_uvt (uv,t)})
        else vs_exp e uvonly cont

and vs_exp (e:exp) (uvonly:bool) (cont:(freevars * uvars) -> 'res) : 'res = 
    match !e.fvs, !e.uvs with
    | Some _, None -> failwith "Impossible"
    | None, None -> vs_exp' e uvonly (fun fvs -> stash uvonly e fvs; cont fvs)
    | None, Some uvs -> 
        if uvonly 
        then cont (no_fvs, uvs)
        else vs_exp' e uvonly (fun fvs -> stash uvonly e fvs; cont fvs)
    | Some fvs, Some uvs -> cont (fvs, uvs)
    
and vs_comp' (c:comp) (uvonly:bool) (k:(freevars * uvars) -> 'res) : 'res = 
    let c = compress_comp c in
    match c.n with 
        | Total t 
        | Rigid t -> vs_typ t uvonly k
         
        | Flex(t, t') -> 
          vs_prod_tt uvonly None t t' k

        | Comp ct -> 
          if uvonly
          then vs_typ ct.result_typ uvonly k
          else vs_either_l (Inl ct.result_typ::ct.effect_args) uvonly k

and vs_comp (c:comp) (uvonly:bool) (cont:(freevars * uvars) -> 'res) : 'res = 
    match !c.fvs, !c.uvs with 
    | Some _, None -> failwith "Impossible"
    | None, None -> vs_comp' c uvonly (fun fvs -> stash uvonly c fvs; cont fvs)
    | None, Some uvs -> 
        if uvonly
        then cont (no_fvs, uvs)
        else vs_comp' c uvonly (fun fvs -> stash uvonly c fvs; cont fvs)
    | Some fvs, Some uvs -> cont (fvs, uvs)

and vs_either (te:either<typ,exp>) (uvonly:bool) (cont:(freevars * uvars) -> 'res) : 'res = 
    match te with 
        | Inl t -> vs_typ t uvonly cont
        | Inr e -> vs_exp e uvonly cont

and vs_either_l (tes:list<either<typ,exp>>) (uvonly:bool) (cont:(freevars * uvars) -> 'res) : 'res = 
    match tes with 
        | [] -> cont (no_fvs, no_uvs)
        | hd::tl -> 
          vs_either hd uvonly (fun ft1 -> 
          vs_either_l tl uvonly (fun ft2 -> 
          cont (union_fvs ft1 ft2)))

//let freevars_kind (k:knd) : freevars' = 
//   vs_kind k false (fun (x,_) -> (Util.set_elements x.ftvs, Util.set_elements x.fxvs))
//      
//let freevars_typ (t:typ) : freevars' = 
//   vs_typ t false (fun (x,_) -> (Util.set_elements x.ftvs, Util.set_elements x.fxvs))
// 
//let freevars_exp (e:exp) : freevars' =
//   vs_exp e false (fun (x,_) -> (Util.set_elements x.ftvs, Util.set_elements x.fxvs))
// 
//let freevars_comp c : freevars' = 
//   vs_comp c false (fun (x,_) -> (Util.set_elements x.ftvs, Util.set_elements x.fxvs))

let freevars_kind (k:knd) : freevars = 
   vs_kind k false (fun (x,_) -> x)
      
let freevars_typ (t:typ) : freevars = 
   vs_typ t false (fun (x,_) -> x)
 
let freevars_exp (e:exp) : freevars =
   vs_exp e false (fun (x,_) -> x)
 
let freevars_comp c : freevars = 
   vs_comp c false (fun (x,_) -> x)

let is_free axs (fvs:freevars) = 
  axs |> Util.for_some (function 
    | Inl a -> Util.set_mem a fvs.ftvs
    | Inr x -> Util.set_mem x fvs.fxvs)

let rec update_uvars (s:syntax<'a,'b>) (uvs:uvars) =
  let out = (Util.set_elements uvs.uvars_k) |> List.fold_left (fun out u -> 
        match Unionfind.find u with 
            | Fixed k -> union_uvs (uvars_in_kind k) out
            | _ -> {out with uvars_k=set_add u (out.uvars_k)}) no_uvs in
  let out = (Util.set_elements uvs.uvars_t) |> List.fold_left (fun out (u,t) -> 
        match Unionfind.find u with 
            | Fixed t -> union_uvs (uvars_in_typ t) out
            | _ -> {out with uvars_t=set_add (u,t) out.uvars_t}) out in
  let out = (Util.set_elements uvs.uvars_e) |> List.fold_left (fun out (u,t) -> 
        match Unionfind.find u with 
            | Fixed e -> union_uvs (uvars_in_exp e) out
            | _ -> {out with uvars_e=set_add (u,t) out.uvars_e}) out in
  s.uvs := Some out;
  out

and uvars_in_kind k : uvars = 
  update_uvars k <| vs_kind k true (fun (_,x) -> x) 
  
and uvars_in_typ t : uvars = 
  update_uvars t <| vs_typ t true (fun (_,x) -> x)

and uvars_in_exp e : uvars = 
  update_uvars e <| vs_exp e true (fun (_,x) -> x) 

and uvars_in_comp c : uvars = 
  update_uvars c <| vs_comp c true (fun (_,x) -> x) 
  
(***********************************************************************************************)
(* closing types and terms *)
(***********************************************************************************************)
let mk_curried_tlam vars t =
    List.fold_right (fun ax t -> match ax with 
        | Inl a -> mk_Typ_tlam(a.v, a.sort, t) (mk_Kind_tcon(Some a.v, a.sort, t.tk, false) t.pos) t.pos
        | Inr x -> mk_Typ_lam(x.v, x.sort, t) (mk_Kind_dcon(Some x.v, x.sort, t.tk, false) t.pos) t.pos) vars t

let mk_curried_lam vars e = 
    List.fold_right (fun ax e -> match ax with 
        | Inl a -> mk_Exp_tabs(a.v, a.sort, e) (mk_Typ_univ(a.v, a.sort, mk_Total e.tk) ktype e.pos) e.pos
        | Inr x -> mk_Exp_abs(x.v, x.sort, e) (mk_Typ_fun(Some x.v, x.sort, mk_Total e.tk, false) ktype e.pos) e.pos) vars e

let rec close_for_kind t k = 
    let k = compress_kind k in 
    match k.n with 
    | Kind_unknown
    | Kind_type
    | Kind_effect
    | Kind_uvar _ -> t
    | Kind_dcon(None, t0, k', _) -> mk_Typ_lam(new_bvd None, t0, close_for_kind t k') k t.pos
    | Kind_dcon(Some x, t0, k', _) -> mk_Typ_lam(x, t0, close_for_kind t k') k t.pos
    | Kind_tcon(None, k0, k', _) -> mk_Typ_tlam(new_bvd None, k0, close_for_kind t k') k t.pos
    | Kind_tcon(Some a, k0, k', _) -> mk_Typ_tlam(a, k0, close_for_kind t k') k t.pos
    | Kind_abbrev(_, k) -> close_for_kind t k
    | Kind_delayed _ -> failwith "Impossible"

let close_with_lam tps t = List.fold_right
  (fun tp out -> match tp with
    | Tparam_typ (a,k) -> mk_Typ_tlam (a,k,out) (mk_Kind_tcon(Some a, k, out.tk, false) out.pos) out.pos
    | Tparam_term (x,t) -> mk_Typ_lam (x,t,out) (mk_Kind_dcon(Some x, t, out.tk, false) out.pos) out.pos)
  tps t 

let close_with_arrow tps t =
  t |> (tps |> List.fold_right (
    fun tp out -> match tp with
      | Tparam_typ (a,k) -> mk_Typ_univ (a, k, total_comp out (range_of_bvd a)) mk_Kind_type out.pos
      | Tparam_term (x,t) -> mk_Typ_fun (Some x, t, total_comp out (range_of_bvd x), true) mk_Kind_type out.pos))

let close_typ = close_with_arrow
      
let close_kind tps k = 
    List.fold_right 
        (fun tp k -> match tp with
            | Tparam_typ (a, k') -> mk_Kind_tcon(Some a, k', k, false) k.pos
            | Tparam_term (x, t) -> mk_Kind_dcon(Some x, t, k, false) k.pos)
        tps k 

(********************************************************************************)
(******************************** Alpha conversion ******************************)
(********************************************************************************)
let freshen_label ropt _ e = match ropt with
  | None -> e
  | Some r ->
    let rstr = Range.string_of_range r in
    match (unascribe e).n with
      | Exp_constant(Const_string(bytes, p)) ->
        let bytes =  Util.unicode_of_string (Util.string_of_unicode bytes ^ " : " ^ rstr) in
        mk_Exp_constant(Const_string(bytes, p)) e.tk e.pos
      | _ -> e 

(********************************************************************************)
(******************** Reducing to weak head normal form *************************)
(***********************(inefficient--see tc/normalize.fs)***********************)

let whnf t =
  let rec aux ctr t =
    let t = compress_typ t in
    let t' = match t.n with
      | Typ_dep(t1, e, imp) ->
        let t1,ctr = aux (ctr+1) t1 in
        (match t1.n with
          | Typ_lam(x, t1_a, t1_r) ->
            let t1_r' = subst_typ (mk_subst [Inr(x,e)]) t1_r in
            aux (ctr+1) t1_r'
          | _ -> mk_Typ_dep(t1, e, imp) t.tk t.pos, ctr)
      | Typ_app(t1, t2, imp) ->
        let t1,ctr = aux (ctr+1) t1 in
        let t2,ctr = aux (ctr+1) t2 in
        (match t1.n with
          | Typ_tlam(a, t1_a, t1_r) ->
            let t1_r' = subst_typ (mk_subst [Inl(a,t2)]) t1_r in
            aux (ctr+1) t1_r'
          | _ -> mk_Typ_app(t1, t2, imp) t.tk t.pos, ctr)
      | _ -> t, ctr in
    t' in
  fst (aux 0 t)

(********************************************************************************)
(*********************** Various tests on constants  ****************************)
(********************************************************************************)
let is_tuple_constructor (t:typ) = match t.n with 
  | Typ_const l -> Util.starts_with l.v.str "Prims.Tuple"
  | _ -> false

let mk_tuple_lid n r = 
  let t = Util.format1 "Tuple%s" (Util.string_of_int n) in
  set_lid_range (Const.pconst t) r

let mk_tuple_data_lid n r = 
  let t = Util.format1 "MkTuple%s" (Util.string_of_int n) in
  set_lid_range (Const.pconst t) r

let is_dtuple_constructor (t:typ) = match t.n with 
  | Typ_const l -> Util.starts_with l.v.str "Prims.DTuple"
  | _ -> false

let mk_dtuple_lid n r = 
  let t = Util.format1 "DTuple%s" (Util.string_of_int n) in
  set_lid_range (Const.pconst t) r 

let mk_dtuple_data_lid n r = 
  let t = Util.format1 "MkDTuple%s" (Util.string_of_int n) in
  set_lid_range (Const.pconst t) r


let is_lid_equality x =
  (lid_equals x Const.eq_lid) ||
    (lid_equals x Const.eq2_lid) ||
    (lid_equals x Const.eqA_lid) ||
    (lid_equals x Const.eqT_lid)

let is_forall lid = lid_equals lid Const.forall_lid || lid_equals lid Const.allTyp_lid
let is_exists lid = lid_equals lid Const.exists_lid || lid_equals lid Const.exTyp_lid
let is_qlid lid   = is_forall lid || is_exists lid
let is_equality x = is_lid_equality x.v

let lid_is_connective =
  let lst = [Const.and_lid; Const.or_lid; Const.not_lid;
             Const.iff_lid; Const.imp_lid] in
  fun lid -> Util.for_some (lid_equals lid) lst
    
let is_constructor t lid =
  match (pre_typ t).n with
    | Typ_const tc -> lid_equals tc.v lid
    | _ -> false
      
let rec is_constructed_typ t lid = match (pre_typ t).n with
  | Typ_const _ -> is_constructor t lid
  | Typ_app(t, _, _)
  | Typ_dep(t, _, _) -> is_constructed_typ t lid
  | _ -> false

let rec get_tycon t = 
  let t = pre_typ t in
  match t.n with
  | Typ_btvar _ 
  | Typ_const _  -> Some t
  | Typ_app(t, _, _)
  | Typ_dep(t, _, _) -> get_tycon t
  | _ -> None

let rec is_function_typ t = 
  match (compress_typ t).n with 
    | Typ_fun _ 
    | Typ_univ _ -> true
    | _ -> false

let base_kind = function
  | Kind_type -> true
  | _ -> false

let sortByFieldName (fn_a_l:list<(fieldname * 'a)>) =
  fn_a_l |> List.sortWith
      (fun (fn1, _) (fn2, _) ->
        String.compare
          (text_of_lid fn1)
          (text_of_lid fn2))
    
let mk_tlam xopt t1 t2 = match xopt with
  | None ->  mk_Typ_lam(new_bvd None, t1, t2) (mk_Kind_dcon(None, t1, t2.tk, false) t2.pos) t2.pos
  | Some x-> mk_Typ_lam(x, t1, t2) (mk_Kind_dcon(Some x, t1, t2.tk, false) t2.pos) t2.pos

let mkRefinedUnit formula =
  let bvd = new_bvd None in
  let t = mk_Typ_refine(bvd, ftv Const.unit_lid ktype, formula) mk_Kind_type formula.pos in
  t, bvd.realname

let findValDecl (vds:list<sigelt>) bvd : option<sigelt> =
  vds |> Util.find_opt (function
                         | Sig_val_decl(lid, t, _, _) -> lid.ident.idText = bvd.ppname.idText
                         | _ -> false)
      
let rec typs_of_letbinding x = match x with
  | (_, t, e)::tl -> t::typs_of_letbinding tl
  | _ -> []

let kt_kt = Const.kunary ktype ktype
let kt_kt_kt = Const.kbin ktype ktype ktype
let mk_conj_opt phi1 phi2 = match phi1 with
  | None -> Some phi2
  | Some phi1 ->
    let app1 = mk_Typ_app(ftv Const.and_lid kt_kt_kt, phi1, false) kt_kt phi1.pos in
    let and_t = mk_Typ_app(app1, phi2, false) ktype (Range.union_ranges phi1.pos phi2.pos) in
    Some and_t

let mk_binop op phi1 phi2 = 
  let app1 = mk_Typ_app(ftv op kt_kt_kt, phi1, false) kt_kt phi1.pos in
  mk_Typ_app(app1, phi2, false) ktype (Range.union_ranges phi1.pos phi2.pos)

let mk_neg phi = mk_Typ_app(ftv Const.not_lid kt_kt, phi, false) ktype phi.pos
let mk_conj phi1 phi2 = mk_binop Const.and_lid phi1 phi2
let mk_disj phi1 phi2 = mk_binop Const.or_lid phi1 phi2
let mk_imp phi1 phi2  = mk_binop Const.imp_lid phi1 phi2
let mk_iff phi1 phi2  = mk_binop Const.iff_lid phi1 phi2
let eq_k = 
    let a = new_bvd None in 
    let atyp = bvd_to_typ a ktype in
    let b = new_bvd None in 
    let btyp = bvd_to_typ b ktype in
    mk_Kind_tcon(Some a, ktype, 
            mk_Kind_tcon(Some b, ktype, 
                mk_Kind_dcon(None, atyp, 
                    mk_Kind_dcon(None, btyp, ktype, false) dummyRange, false) dummyRange, true) dummyRange, true) dummyRange

let mk_eq e1 e2       = 
  let eqk2 = mk_Kind_dcon(None, e2.tk, ktype, false) dummyRange in 
  let app1 = mk_Typ_dep(ftv Const.eq2_lid eq_k, e1, false) eqk2 e1.pos in
  mk_Typ_dep(app1, e2, false) ktype (Range.union_ranges e1.pos e2.pos)

let normalizeRefinement t =
  let rec aux xopt t = match t.n with
    | Typ_refine(bvd, t', phi) ->
      let x, phi = match xopt with
        | None ->
          Some (bvd_to_exp bvd t'), phi
        | Some x ->
          xopt, subst_typ (mk_subst [Inr(bvd,x)]) phi in
      let t', phi_opt = aux xopt t' in
      t', mk_conj_opt phi_opt phi
    | _ -> t, None in
  aux None t
 
let forall_kind_t atyp =
    mk_Kind_tcon(None, mk_Kind_dcon(None, atyp, mk_Kind_type, false) dummyRange,
                mk_Kind_type, 
                false) dummyRange
 
 let forall_kind =
  let a = new_bvd None in
  let atyp = bvd_to_typ a mk_Kind_type in
    mk_Kind_tcon(Some a, mk_Kind_type, forall_kind_t atyp, true) dummyRange

let mk_forallT a k b = 
  let r = dummyRange in
  let allT_k = mk_Kind_tcon(None, mk_Kind_tcon(Some a, k, ktype, false) r, ktype, false) r in 
  let forall_typ = ftv Const.allTyp_lid allT_k in
  mk_Typ_app(forall_typ, mk_Typ_tlam(a, k, b) (mk_Kind_tcon(Some a, k, b.tk, false) r) r, false) ktype r
 
let mk_forall (x:bvvdef) (a:typ) (body:typ) : typ =
  let r = dummyRange in
  let forall_typ = ftv Const.forall_lid forall_kind in 
  mk_Typ_app(mk_Typ_app(forall_typ, a, true) (forall_kind_t a) r, 
            mk_Typ_lam(x, a, body) (mk_Kind_dcon(Some x, a, body.tk, false) r) r, false) mk_Kind_type r
  
let un_forall t = match t.n with
  | Typ_app({n=Typ_app({n=Typ_const(lid)}, _, _)}, 
            {n=Typ_lam(x, t, body)}, _) when is_forall lid.v ->
    Some (x, t, body)
  | _ -> None

(* collect all curried arguments until we reach a non-trivial computation type *)
let collect_formals t = 
  let rec aux out t =
      match (compress_typ t).n with
        | Typ_fun(xopt, t1, cod, imp) -> 
          let out = Inr(xopt,t1,imp)::out in
          if is_total_comp cod
          then aux out (comp_result cod)
          else List.rev out, cod
        | Typ_univ(a, k, cod) -> 
          let out = Inl(a,k)::out in
          if is_total_comp cod 
          then aux out (comp_result cod)
          else List.rev out, cod
        | _ -> List.rev out, mk_Total t 
  in aux [] t

let collect_formals_k k =
    let rec aux out k = 
        let k = compress_kind k in 
        match k.n with 
            | Kind_tcon(aopt, k, k', imp) ->
              aux (Inl(aopt, k, imp)::out) k'
            | Kind_dcon(xopt, t, k', imp) ->
              aux (Inr(xopt, t, imp)::out) k'
            | Kind_abbrev(_, k) -> aux out k
            | _ -> List.rev out, k
    in aux [] k

let collect_forall_xt t =
  let rec aux out t =
    match flatten_typ_apps (whnf t) with //NS: Should this really be doing whnf? Try to remove
      | {n=Typ_const tc}, [Inl t1; Inl ({n=Typ_lam(x, _, t2)})]
        when is_forall tc.v ->
        aux (Inr(x, t1)::out) t2
      | {n=Typ_const tc}, [Inl ({n=Typ_tlam(a, k, t2)})]
          when (lid_equals tc.v Const.allTyp_lid) ->
          aux (Inl(a,k)::out) t2
      | _ -> List.rev out, t
  in aux [] t

let collect_exists_xt t =
  let rec aux out t =
      match flatten_typ_apps (whnf t) with  //NS: Should this really be doing whnf? Try to remove
        | {n=Typ_const tc}, [Inl t1; Inl ({n=Typ_lam(x, _, t2)})]
          when lid_equals tc.v Const.exists_lid ->
          aux (Inr(x, t1)::out) t2
        | {n=Typ_const tc}, [Inl ({n=Typ_tlam(a, k, t2)})]
          when (lid_equals tc.v Const.exTyp_lid) ->
          aux (Inl(a,k)::out) t2
        | _ -> List.rev out, t
  in aux [] t
  
let rec is_wild_pat p =
    match p with
    | Pat_wild -> true
    | Pat_withinfo (p, _) -> is_wild_pat p
    | _ -> false

let mangle_field_name x = mk_ident("^fname^" ^ x.idText, x.idRange) 
let unmangle_field_name x = 
    if Util.starts_with x.idText "^fname^"
    then mk_ident(Util.substring_from x.idText 7, x.idRange)
    else x

(**************************************************************************************)
(* Destructing a type as a formula *)
(**************************************************************************************)
type qpats = list<either<typ,exp>>
type connective = 
    | QAll of list<either<(btvdef*knd), (bvvdef*typ)>> * qpats * typ
    | QEx of list<either<(btvdef*knd), (bvvdef*typ)>> * qpats * typ
    | BaseConn of lident * list<either<typ,exp>>

let destruct_typ_as_formula f : option<connective> = 
    let destruct_base_conn f = 
        let type_sort, term_sort = true, false in
        let oneType    = [type_sort] in
        let twoTypes   = [type_sort;type_sort] in
        let threeTys   = [type_sort;type_sort;type_sort] in
        let twoTerms   = [term_sort;term_sort] in
        let connectives = [ (Const.true_lid, []);
                            (Const.false_lid, []);
                            (Const.and_lid, twoTypes);
                            (Const.or_lid,  twoTypes);
                            (Const.imp_lid, twoTypes);
                            (Const.iff_lid, twoTypes);
                            (Const.ite_lid, threeTys);
                            (Const.not_lid, oneType);
                            (Const.lt_lid,  twoTerms);
                            (Const.gt_lid,  twoTerms);
                            (Const.gte_lid, twoTerms);
                            (Const.lte_lid, twoTerms);
                            (Const.eqT_lid, twoTypes);
                            (Const.eq2_lid, twoTerms);
                            (Const.eq2_lid, twoTypes@twoTerms);
                        ] in 
        let rec aux f (lid, arity) =  
        let t, args = flatten_typ_apps f in 
        if is_constructor t lid 
            && List.length args = List.length arity
            && List.forall2 (fun arg flag -> match arg with 
            | Inl _ -> flag=type_sort
            | Inr _ -> flag=term_sort) args arity
        then Some <| BaseConn(lid, args)
        else None in
        Util.find_map connectives (aux f) in

    let patterns t = 
        let t = compress_typ t in 
        match t.n with 
            | Typ_meta(Meta_pattern(t, pats)) -> pats, compress_typ t
            | _ -> [], compress_typ t in

    let destruct_q_conn t =
        let is_q fa l = if fa then is_forall l else is_exists l in 
        let flat t = 
            let t, args = flatten_typ_apps t in 
            t, args |> List.map (function Inl t -> Inl <| compress_typ t | Inr e -> Inr <| compress_exp e) in
        let rec aux qopt out t = match qopt, flat t with
            | Some fa, ({n=Typ_const tc}, [Inl t1; Inl {n=Typ_lam(x, _, t2)}])  
                when (is_q fa tc.v) ->
              aux qopt (Inr(x, t1)::out) t2

            | Some fa, ({n=Typ_const tc}, [Inl {n=Typ_tlam(a, k, t2)}])
                when (is_q fa tc.v) -> 
              aux qopt (Inl(a, compress_kind k)::out) t2

            | None, ({n=Typ_const tc}, [Inl t1; Inl {n=Typ_lam(x, _, t2)}])  
                when (is_qlid tc.v) -> 
              aux (Some <| is_forall tc.v) (Inr(x, t1)::out) t2
            
            | None, ({n=Typ_const tc}, [Inl {n=Typ_tlam(a, k, t2)}])
                when (is_qlid tc.v) -> 
              aux (Some <| is_forall tc.v) (Inl(a, compress_kind k)::out) t2
            
            | Some true, _ -> 
              let pats, body = patterns t in 
              Some (QAll(List.rev out, pats, body))

            | Some false, _ -> 
              let pats, body = patterns t in 
              Some(QEx(List.rev out, pats, body))

            | _ -> None in
        aux None [] t in

    let phi = compress_typ f in
        match destruct_base_conn phi with 
        | Some b -> Some b
        | None -> destruct_q_conn phi

let comp_to_comp_typ (c:comp) : comp_typ = 
    let c = compress_comp c in 
    match c.n with
        | Flex _
        | Rigid _ -> failwith "Normalize rigid comps before calling"
        | Comp c -> c
        | Total t -> {effect_name=Const.tot_effect_lid; result_typ=t; effect_args=[]; flags=[TOTAL]} 
        


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

open Prims
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
(**************************Utilities for identifiers ****************************)
(********************************************************************************)

let gensym : unit -> string = 
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
let freshen_bvar b =  bvd_to_bvar_s (freshen_bvd b.v) b.sort
let gen_bvar sort = let bvd = (new_bvd None) in bvd_to_bvar_s bvd sort
let gen_bvar_p r sort = let bvd = (new_bvd (Some r)) in bvd_to_bvar_s bvd sort
let bvdef_of_str s = let id = id_of_text s in mkbvd(id, id)
let set_bvd_range bvd r = {ppname=mk_ident(bvd.ppname.idText, r);
                           realname=mk_ident(bvd.realname.idText, r)}
let set_lid_range l r = 
  let ids = (l.ns@[l.ident]) |> List.map (fun i -> mk_ident(i.idText, r)) in
  lid_of_ids ids
let exp_of_lid l t = mk_Exp_fvar (withinfo l t <| range_of_lid l, false) t (range_of_lid l)
let fv l = withinfo l tun (range_of_lid l)
let fvar l r = mk_Exp_fvar(fv (set_lid_range l r), false) tun r
let ftv l k = mk_Typ_const (withinfo l k (range_of_lid l)) k (range_of_lid l)
let order_bvd x y = match x, y with 
  | Inl _, Inr _ -> -1
  | Inr _, Inl _ -> 1
  | Inl x, Inl y -> String.compare x.ppname.idText y.ppname.idText
  | Inr x, Inr y -> String.compare x.ppname.idText y.ppname.idText
let arg_of_non_null_binder (b, imp) = match b with
    | Inl a -> Inl (btvar_to_typ a), imp
    | Inr x -> Inr (bvar_to_exp x), imp

let args_of_non_null_binders (binders:binders) = 
    binders |> List.collect (fun b -> 
        if is_null_binder b then []
        else [arg_of_non_null_binder b])
let args_of_binders (binders:Syntax.binders) : (Syntax.binders * args) =
 binders |> List.map (fun b -> 
    if is_null_binder b 
    then let b = match fst b with
            | Inl a -> 
              Inl <| gen_bvar a.sort, snd b 

            | Inr x -> 
              Inr <| gen_bvar x.sort, snd b 
        in
         b, arg_of_non_null_binder b 
    else b, arg_of_non_null_binder b) |> List.unzip 

let name_binders binders = 
    binders |> List.mapi (fun i b ->
            if is_null_binder b
            then match b with 
                    | Inl a, imp -> 
                      let b = id_of_text ("_" ^ string_of_int i) in
                      let b = bvd_to_bvar_s (mkbvd(b,b)) a.sort in
                      Inl b, imp

                    | Inr y, imp -> 
                      let x = id_of_text ("_" ^ string_of_int i) in
                      let x = bvd_to_bvar_s (mkbvd(x,x)) y.sort in
                      Inr x, imp
            else b)
             
let name_function_binders t = match t.n with 
    | Typ_fun(binders, comp) -> mk_Typ_fun(name_binders binders, comp) t.tk t.pos
    | _ -> t
let null_binders_of_args (args:args) : binders = 
    args |> List.map (fun (a, imp) -> match a with 
        | Inl t -> fst <| null_t_binder t.tk, imp 
        | Inr v -> fst <| null_v_binder v.tk, imp)
let binders_of_args (args:args) : binders = 
    args |> List.map (fun (a, imp) -> match a with 
        | Inl t -> Inl (gen_bvar_p t.pos t.tk), imp 
        | Inr v -> Inr (gen_bvar_p v.pos v.tk), imp)

let binders_of_freevars fvs = 
    (Util.set_elements fvs.ftvs |> List.map t_binder)@
    (Util.set_elements fvs.fxvs |> List.map v_binder)

(********************************************************************************)
(*************************** Delayed substitutions ******************************)
(********************************************************************************)
let subst_to_string s = 
  s |> List.map (function Inl (b, _) -> b.realname.idText | Inr (x, _) -> x.realname.idText) |> String.concat ", "

(* delayed substitutions *)
let subst_tvar s t = match t.n with 
  | Typ_btvar a -> 
    begin match Util.find_opt (function Inl (b, _) -> bvd_eq b a.v | _ -> false) s with 
      | Some (Inl(_, t)) -> t
      | _ -> t
    end
  | _ -> failwith "impossible"
let subst_xvar s e = match e.n with
  | Exp_bvar x -> 
    begin match Util.find_opt (function Inr(y, _) -> bvd_eq y x.v | _ -> false) s with
            | Some (Inr(_, e)) -> e
            | _ -> e
    end
  | _ -> failwith "impossible"
let rec subst_typ s t = match s with 
  | [] -> t
  | _ -> 
    let t0 = Visit.compress_typ t in
    match t0.n with 
    | Typ_delayed(t', s', m) -> mk_Typ_delayed (t', compose_subst s' s, Util.mk_ref None) t.tk t.pos
    | Typ_btvar a -> subst_tvar s t0
    | _ -> mk_Typ_delayed(t, s, Util.mk_ref None) t.tk t.pos

and subst_exp s e = match s with 
  | [] -> e
  | _ -> 
    let e0 = Visit.compress_exp e in
    match e0.n with
    | Exp_delayed(e, s',m) -> mk_Exp_delayed (e, compose_subst s' s, Util.mk_ref None) e.tk e.pos
    | Exp_bvar _ -> subst_xvar s e0
    | _ -> mk_Exp_delayed (e0, s, Util.mk_ref None) e0.tk e0.pos

and subst_kind s k = match s with 
  | [] -> k 
  | _ -> 
  let k0 = Visit.compress_kind k in
    match k0.n with
    | Kind_type
    | Kind_effect
    | Kind_unknown -> k0
    | Kind_delayed(k, s',m) -> mk_Kind_delayed(k, compose_subst s' s, Util.mk_ref None) k0.pos
    | _ -> mk_Kind_delayed(k0, s, Util.mk_ref None) k0.pos

and subst_comp_typ s t = match s with 
  | [] -> t
  | _ -> 
    {t with result_typ=subst_typ s t.result_typ; 
            effect_args=List.map (function Inl t, imp -> Inl <| subst_typ s t, imp | Inr e, imp -> Inr <| subst_exp s e, imp) t.effect_args}
and subst_comp s t = match s with 
  | [] -> t
  | _ -> 
    match t.n with 
      | Total t -> mk_Total (subst_typ s t)
      | Comp ct -> mk_Comp(subst_comp_typ s ct)

and compose_subst (s1:subst) (s2:subst) = 
  mk_subst <| ((s1 |> List.map (function 
      | Inl(x, t) -> Inl (x, subst_typ s2 t)
      | Inr(x, e) -> Inr (x, subst_exp s2 e)))@s2)

let subst_kind' s t = subst_kind (mk_subst s) t
let subst_typ' s t = subst_typ (mk_subst s) t
let subst_exp' s t = subst_exp (mk_subst s) t
let subst_comp' s t = subst_comp (mk_subst s) t
let subst_binder s = function
    | Inl a, imp -> Inl ({a with sort=subst_kind s a.sort}), imp
    | Inr x, imp -> Inr ({x with sort=subst_typ s x.sort}), imp
let subst_arg s = function 
    | Inl t, imp -> Inl (subst_typ s t), imp
    | Inr e, imp -> Inr (subst_exp s e), imp
let subst_binders s bs = match s with 
    | [] -> bs
    | _ -> List.map (subst_binder s) bs
let subst_args s args = match s with 
    | [] -> args
    | _ -> List.map (subst_arg s) args
let subst_formal (f:binder) (a:arg) = match f, a with 
    | (Inl a, _), (Inl t, _) -> Inl(a.v, t)
    | (Inr x, _), (Inr v, _) -> Inr(x.v, v)
    | _ -> failwith "Ill-formed substitution"

let subst_of_list (formals:binders) (actuals:args) : subst = 
    if (List.length formals = List.length actuals)
    then List.map2 subst_formal formals actuals |> mk_subst
    else failwith "Ill-formed substitution"

let restrict_subst axs s = //s ... NS: Not clear that it's worth restricting a subst, particularly as we are also alpha converting
  s |> List.filter (fun b ->
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
and map_comp s mk map_typ map_exp descend binders c = match c.n with 
    | Total t -> 
      let t, descend = map_typ descend binders t in
      mk_Total t, descend
    | Comp ct ->
      let t, descend = map_typ descend binders ct.result_typ in
      let args, descend = Visit.map_args map_typ map_exp descend binders ct.effect_args in 
      mk_Comp ({ct with result_typ=t; effect_args=args}), descend 
and visit_knd s vk mt me ctrl binders k = 
  let k = Visit.compress_kind k in 
  if ctrl.descend 
  then let k, _ = vk null_ctrl binders k in k, ctrl
  else map_knd s vk mt me null_ctrl binders k
and visit_typ s mk vt me ctrl (boundvars:Visit.boundvars) t = 
  let visit_prod (bs:binders) tc = 
    let bs, boundvars, s = bs |> List.fold_left (fun (bs, boundvars, s) b -> match b with
        | Inl a, imp -> 
          let k, _ = map_knd s mk vt me null_ctrl boundvars a.sort in
          let a = {a with sort=k} in
          if is_null_binder b
          then (Inl a, imp)::bs, boundvars, s
          else 
              let boundvars' = Inl a.v::boundvars in
              let s = restrict_subst boundvars' s in
              let b, s, boundvars = match s with 
                | [] when ctrl.stop_if_empty_subst -> Inl a, s, boundvars'
                | _ -> 
                    let b = bvd_to_bvar_s (freshen_bvd a.v) k in
                    let s = extend_subst (Inl(a.v, btvar_to_typ b)) s in
                    Inl b, s, Inl b.v::boundvars in
              (b,imp)::bs, boundvars, s
          
        | Inr x, imp -> 
          let t, _ = map_typ s mk vt me null_ctrl boundvars x.sort in
          let x = {x with sort=t} in
          if is_null_binder b
          then (Inr x, imp)::bs, boundvars, s
          else 
              let boundvars' = Inr x.v::boundvars in
              let s = restrict_subst boundvars' s in
              let b, s, boundvars = match s with 
                | [] when ctrl.stop_if_empty_subst -> Inr x, s, boundvars'
                | _ -> 
                    let y = bvd_to_bvar_s (freshen_bvd x.v) t in
                    let s = extend_subst (Inr(x.v, bvar_to_exp y)) s in
                    Inr y, s, Inr y.v::boundvars in
              (b,imp)::bs, boundvars, s) ([], boundvars, s) in

    let tc = match s, tc with 
        | [], _ -> tc
        | _, Inl t -> Inl (fst <| map_typ s mk vt me null_ctrl boundvars t)
        | _, Inr c -> Inr (fst <| map_comp s mk (map_typ s mk vt me) (map_exp s mk vt me) null_ctrl boundvars c) in
    List.rev bs, tc  in

  let t0 = t in
  match t0.n with
    | Typ_btvar a -> 
      //printfn "Trying to subst. %s with [%s]\n" (a.v.realname.idText) (s |> subst_to_string);
      compress_typ <| subst_tvar (restrict_subst boundvars s) t, ctrl
    
    | _ when (not ctrl.descend) -> map_typ s mk vt me null_ctrl boundvars t

     (* all the binding forms need to be alpha-converted to avoid capture *)
    | Typ_fun(bs, c) -> 
        (match visit_prod bs (Inr c) with 
            | bs, Inr c -> mk_Typ_fun (bs, c) t0.tk t0.pos, ctrl
            | _ -> failwith "Impossible")

    | Typ_refine(x, t) -> 
        (match visit_prod [Inr x, false] (Inl t) with 
            | [(Inr x, _)], Inl t -> mk_Typ_refine(x, t) t0.tk t0.pos, ctrl
            | _ -> failwith "Impossible")
    
    | Typ_lam(bs, t) ->
        (match visit_prod bs (Inl t) with 
            | bs, Inl t -> mk_Typ_lam(bs, t) t0.tk t0.pos, ctrl
            | _ -> failwith "Impossible")
        
    | _ -> let t, _ = vt null_ctrl boundvars t in t, ctrl
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
    let k' = compress_kind k' in
    m := Some k'; 
    k'
  | Kind_uvar(uv, actuals) -> 
    begin match Unionfind.find uv with 
        | Fixed k -> 
            (match k.n with
                | Kind_lam(formals, k') -> 
                  compress_kind (subst_kind (subst_of_list formals actuals) k')
                | _ -> 
                    if List.length actuals = 0
                    then k
                    else failwith "Wrong arity for kind unifier")
        | _ -> k
    end
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

let rec unmeta_exp e =
    let e = compress_exp e in 
    match e.n with 
        | Exp_meta(Meta_desugared(e, _)) 
        | Exp_meta(Meta_datainst(e, _)) -> unmeta_exp e
        | Exp_ascribed(e, _) -> unmeta_exp e
        | _ -> e

let rec unmeta_typ t =
    let t = compress_typ t in
    match t.n with 
        | Typ_ascribed(t, _) 
        | Typ_meta(Meta_named(t, _))
        | Typ_meta(Meta_pattern(t, _))
        | Typ_meta(Meta_labeled(t, _, _))
        | Typ_meta(Meta_refresh_label(t, _, _)) -> unmeta_typ t
        | _ -> t

let alpha_typ t = 
   let t = compress_typ t in
   let s = mk_subst [] in
   let doit t = fst <| Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) Visit.combine_kind Visit.combine_typ Visit.combine_exp alpha_ctrl [] t  in
   match t.n with 
    | Typ_lam(bs, _)
    | Typ_fun(bs, _) -> if Util.for_all is_null_binder bs then t else doit t
    | Typ_refine _  -> doit t
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

let comp_set_flags (c:comp) f = match c.n with 
  | Total _ -> c
  | Comp ct -> {c with n=Comp ({ct with flags=f})}

let comp_flags c = match c.n with 
  | Total _ -> [TOTAL]
  | Comp ct -> ct.flags

let is_total_comp c = comp_flags c |> Util.for_some (function TOTAL | RETURN -> true | _ -> false)

let is_pure_comp c = match c.n with 
    | Total _ -> true
    | Comp ct -> is_total_comp c 
                 || Util.starts_with ct.effect_name.str "Prims.PURE"
                 || List.contains LEMMA ct.flags
                 
let is_pure_function t = match (compress_typ t).n with 
    | Typ_fun(_, c) -> is_pure_comp c
    | _ -> true

let is_lemma t = match (compress_typ t).n with 
    | Typ_fun(_, c) -> (match c.n with 
        | Comp ct -> lid_equals ct.effect_name Const.lemma_lid
        | _ -> false)
    | _ -> false

let is_ml_comp c = match c.n with
  | Comp c -> lid_equals c.effect_name Const.ml_effect_lid || List.contains MLEFFECT c.flags
  | _ -> false

let comp_result c = match c.n with 
  | Total t -> t
  | Comp ct -> ct.result_typ

let set_result_typ c t = match c.n with 
  | Total _ -> mk_Total t
  | Comp ct -> mk_Comp({ct with result_typ=t})

let is_trivial_wp c = 
  comp_flags c |> Util.for_some (function TOTAL | RETURN -> true | _ -> false)
  
(********************************************************************************)
(****************Simple utils on the local structure of a term ******************)
(********************************************************************************)
let rec is_atom e = match (compress_exp e).n with
    | Exp_bvar _ 
    | Exp_fvar _ 
    | Exp_constant _ -> true
    | Exp_meta (Meta_desugared(e, _))
    | Exp_meta (Meta_datainst(e, _)) -> is_atom e
    | _ -> false
     
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

let unascribe_either = function 
    | Inl t -> Inl <| unascribe_typ (compress_typ t)
    | Inr e -> Inr <| unascribe (compress_exp e)

let rec unrefine t = 
  let t = compress_typ t in
  match t.n with
      | Typ_refine(x, _) -> unrefine x.sort
      | _ -> t

let is_fun e = match (compress_exp e).n with 
  | Exp_abs _ -> true
  | _ -> false

let rec pre_typ t = 
    let t = compress_typ t in 
    match t.n with 
      | Typ_refine(x, _) -> pre_typ x.sort 
      | Typ_ascribed(t, _) -> pre_typ t
      | _ -> t

let destruct typ lid = 
  let typ = compress_typ typ in
  match typ.n with 
    | Typ_app({n=Typ_const tc}, args) when lid_equals tc.v lid -> Some args
    | Typ_const tc when lid_equals tc.v lid -> Some[]
    | _ -> None

let rec lids_of_sigelt se = match se with 
  | Sig_let(_, _, lids) 
  | Sig_bundle(_, _, lids)
  | Sig_monads(_, _, _, lids) -> lids
  | Sig_tycon (lid, _, _,  _, _, _, _)    
  | Sig_typ_abbrev  (lid, _, _, _, _, _)
  | Sig_datacon (lid, _, _, _, _)
  | Sig_val_decl (lid, _, _, _) 
  | Sig_assume (lid, _, _, _) -> [lid]
  | Sig_main _ -> []
    
let lid_of_sigelt se : option<lident> = match lids_of_sigelt se with
  | [l] -> Some l
  | _ -> None

let range_of_sigelt x = match x with 
  | Sig_bundle(_, r, _) 
  | Sig_tycon (_, _, _,  _, _, _, r)    
  | Sig_typ_abbrev  (_, _, _, _, _, r)
  | Sig_datacon (_, _, _, _, r)
  | Sig_val_decl (_, _, _, r) 
  | Sig_assume (_, _, _, r)
  | Sig_let(_, r, _) 
  | Sig_main(_, r) 
  | Sig_monads(_, _, r, _) -> r

let range_of_lb = function
  | (Inl x, _, _) -> range_of_bvd x
  | (Inr l, _, _) -> range_of_lid l 

let range_of_args args r = 
   args |> List.fold_left (fun r -> function 
    | (Inl hd, _) -> Range.union_ranges r hd.pos
    | (Inr hd, _) -> Range.union_ranges r hd.pos) r 

let mk_typ_app f args = 
    let r = range_of_args args f.pos in
    let kf = compress_kind f.tk in
    let k = match kf.n with
        | Kind_arrow(bs, k) -> 
          if (List.length bs = List.length args)
          then subst_kind (subst_of_list bs args) k 
          else kun
        | _ -> kun in
    mk_Typ_app(f, args) k r

let mk_exp_app f args = 
  let r = range_of_args args f.pos in
  let tf = compress_typ f.tk in
  let t = match tf.n with 
     | Typ_fun(bs, c) ->
        if List.length bs = List.length args
        then let c = subst_comp (subst_of_list bs args) c in
             comp_result c
        else tun
     | _ -> tun in
  mk_Exp_app(f, args) t r

let mk_data l args = 
  match args with 
    | [] -> 
      mk_Exp_meta(Meta_desugared(fvar l (range_of_lid l), Data_app))
    | _ -> 
      mk_Exp_meta(Meta_desugared(mk_exp_app (fvar l (range_of_lid l)) args, Data_app))

let mangle_field_name x = mk_ident("^fname^" ^ x.idText, x.idRange) 
let unmangle_field_name x = 
    if Util.starts_with x.idText "^fname^"
    then mk_ident(Util.substring_from x.idText 7, x.idRange)
    else x

let mk_field_projector_name lid x i = 
    let nm = if Syntax.is_null_bvar x
             then Syntax.mk_ident("_" ^ Util.string_of_int i, x.p)
             else x.v.ppname in
    let y = {x.v with ppname=nm} in
    lid_of_ids (ids_of_lid lid @ [unmangle_field_name nm]), y

let unchecked_unify uv t = 
  match Unionfind.find uv with 
    | Fixed _ -> failwith "Changing a fixed uvar!"
    | _ -> Unionfind.change uv (Fixed t) (* used to be an alpha-convert t here *)


(********************************************************************************)
(************************* Free type/term/unif variables ************************)
(********************************************************************************)
type bvars = set<btvar> * set<bvvar>
let no_bvars = (Syntax.no_fvs.ftvs, Syntax.no_fvs.fxvs)
let fvs_included fvs1 fvs2 = 
    Util.set_is_subset_of fvs1.ftvs fvs2.ftvs &&
    Util.set_is_subset_of fvs1.fxvs fvs2.fxvs

let eq_fvars v1 v2 = match v1, v2 with 
    | Inl a, Inl b -> Syntax.bvd_eq a b
    | Inr x, Inr y -> Syntax.bvd_eq x y
    | _ -> false

let uv_eq (uv1,_) (uv2,_) = Unionfind.equivalent uv1 uv2
let union_uvs uvs1 uvs2 =
    {   uvars_k=Util.set_union uvs1.uvars_k uvs2.uvars_k;
        uvars_t=Util.set_union uvs1.uvars_t uvs2.uvars_t;
        uvars_e=Util.set_union uvs1.uvars_e uvs2.uvars_e;
    }

let union_fvs (fvs1, uvs1) (fvs2, uvs2) = 
    {
        ftvs=Util.set_union fvs1.ftvs fvs2.ftvs;
        fxvs=Util.set_union fvs1.fxvs fvs2.fxvs;
    }, 
    union_uvs uvs1 uvs2

let sub_fv (fvs, uvs) (tvars, vvars) = 
    {fvs with ftvs=Util.set_difference fvs.ftvs tvars; 
            fxvs=Util.set_difference fvs.fxvs vvars}, 
    uvs

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

        | Typ_uvar (uv, k) -> 
          cont (no_fvs, {no_uvs with uvars_t=single_uvt (uv,k)})

        | Typ_unknown        
        | Typ_const _ -> cont (no_fvs, no_uvs)

        | Typ_fun(bs, c) -> 
          vs_binders bs uvonly (fun (bvs, vs1) -> 
          vs_comp c uvonly (fun vs2 -> 
          cont (sub_fv (union_fvs vs1 vs2) bvs)))

        | Typ_lam(bs, t) -> 
          vs_binders bs uvonly (fun (bvs, vs1) -> 
          vs_typ t uvonly (fun vs2 -> 
          cont (sub_fv (union_fvs vs1 vs2) bvs)))

        | Typ_refine(x, t) -> 
          vs_binders [Inr x, false] uvonly (fun (bvs, vs1) -> 
          vs_typ t uvonly (fun vs2 -> 
          cont (sub_fv (union_fvs vs1 vs2) bvs)))

        | Typ_app(t, args) -> 
          vs_typ t uvonly (fun vs1 -> 
          vs_args args uvonly (fun vs2 ->
          cont (union_fvs vs1 vs2)))

        | Typ_ascribed(t, _) -> 
          vs_typ t uvonly cont        

        | Typ_meta(Meta_refresh_label(t, _, _))
        | Typ_meta(Meta_labeled(t, _, _))
        | Typ_meta(Meta_named(t, _))
        | Typ_meta(Meta_pattern(t, _)) -> 
          vs_typ t uvonly cont


and vs_binders (bs:binders) (uvonly:bool) (cont:(bvars * (freevars * uvars)) -> 'res) : 'res = 
    match bs with 
        | [] -> cont (no_bvars, (no_fvs, no_uvs))

        | (Inl a, _)::rest -> 
           vs_kind a.sort uvonly (fun vs -> 
           vs_binders rest uvonly (fun ((tvars, vvars), vs2) -> 
           cont ((Util.set_add a tvars, vvars), union_fvs vs vs2)))

        | (Inr x, _)::rest -> 
           vs_typ x.sort uvonly (fun vs -> 
           vs_binders rest uvonly (fun ((tvars, vvars), vs2) -> 
           cont ((tvars, Util.set_add x vvars), union_fvs vs vs2)))

and vs_args (args:args) (uvonly:bool) (cont:(freevars * uvars) -> 'res) : 'res = 
    match args with 
        | [] -> cont (no_fvs, no_uvs)
        
        | (Inl t, _)::tl -> 
          vs_typ t uvonly (fun ft1 -> 
          vs_args tl uvonly (fun ft2 -> 
          cont (union_fvs ft1 ft2)))

        | (Inr e, _)::tl -> 
          vs_exp e uvonly (fun ft1 -> 
          vs_args tl uvonly (fun ft2 -> 
          cont (union_fvs ft1 ft2)))


and vs_typ (t:typ) (uvonly:bool) (cont:(freevars * uvars) -> 'res) : 'res = 
    match !t.fvs, !t.uvs with 
        | Some _, None -> failwith "Impossible"
        | None, None -> vs_typ' t uvonly (fun fvs -> stash uvonly t fvs; cont fvs)
        | None, Some uvs -> 
            if uvonly
            then cont (no_fvs, uvs)
            else vs_typ' t uvonly (fun fvs -> stash uvonly t fvs; cont fvs)
        | Some fvs, Some uvs -> cont (fvs, uvs)

and vs_kind' (k:knd) (uvonly:bool) (cont:(freevars * uvars) -> 'res) : 'res = 
    let k = compress_kind k in 
    match k.n with 
        | Kind_lam(_, k) -> failwith (Util.format1 "%s: Impossible ... found a Kind_lam bare" (Range.string_of_range k.pos))
        | Kind_delayed _ -> failwith "Impossible"
        | Kind_unknown
        | Kind_type
        | Kind_effect -> cont (no_fvs, no_uvs)

        | Kind_uvar (uv,args) -> 
          vs_args args uvonly (fun (fvs, uvs) -> 
          cont (fvs, {uvs with uvars_k=Util.set_add uv uvs.uvars_k}))

        | Kind_abbrev(_, k) -> 
          vs_kind k uvonly cont

        | Kind_arrow(bs, k) -> 
          vs_binders bs uvonly (fun (bvs, vs1) -> 
          vs_kind k uvonly (fun vs2 -> 
          cont (sub_fv (union_fvs vs1 vs2) bvs)))

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
    
      | Exp_abs(bs, e) -> 
        vs_binders bs uvonly (fun (bvs, vs1) -> 
        vs_exp e uvonly (fun vs2 -> 
        cont (sub_fv (union_fvs vs1 vs2) bvs)))

      | Exp_app(e, args) -> 
        vs_exp e uvonly (fun ft1 -> 
        vs_args args uvonly (fun ft2 ->
        cont (union_fvs ft1 ft2)))

      | Exp_match _       
      | Exp_let _ -> cont (no_fvs, no_uvs) //failwith "NYI"
                               
      | Exp_meta(Meta_desugared(e, _))
      | Exp_meta(Meta_datainst(e, _)) -> 
        vs_exp e uvonly cont

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
    match c.n with 
        | Total t -> vs_typ t uvonly k
         
        | Comp ct -> 
          if uvonly
          then vs_typ ct.result_typ uvonly k
          else vs_typ ct.result_typ uvonly (fun vs1 -> 
               vs_args ct.effect_args uvonly (fun vs2 -> 
               k (union_fvs vs1 vs2)))

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


(* FYI: using polymorphic mutual recursion here ... need to annotate result type *)
let rec update_uvars (s:syntax<'a,'b>) (uvs:uvars) : uvars =
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
let rec close_for_kind t k = 
    let k = compress_kind k in 
    match k.n with 
    | Kind_lam _ -> failwith "Impossible"
    | Kind_unknown
    | Kind_type
    | Kind_effect
    | Kind_uvar _ -> t
    | Kind_arrow(bs, _) -> mk_Typ_lam(bs, t) k t.pos
    | Kind_abbrev(_, k) -> close_for_kind t k
    | Kind_delayed _ -> failwith "Impossible"

let close_with_lam tps t = 
    match tps with 
        | [] -> t
        | _ -> mk_Typ_lam(tps, t) (mk_Kind_arrow(tps, t.tk) t.pos) t.pos

let close_with_arrow tps t = 
    match tps with 
        | [] -> t
        | _ -> 
          let bs, c = match t.n with
            | Typ_fun(bs', c) -> tps@bs', c
            | _ -> tps, mk_Total t in 
          mk_Typ_fun(bs, c) ktype t.pos

let close_typ = close_with_arrow
      
let close_kind tps k = match tps with 
    | [] -> k
    | _ -> mk_Kind_arrow'(tps, k) k.pos

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

let is_tuple_data_lid f n = 
  Syntax.lid_equals f (mk_tuple_data_lid n Syntax.dummyRange)

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
  | Typ_app(t, _) -> is_constructed_typ t lid
  | _ -> false

let rec get_tycon t = 
  let t = pre_typ t in
  match t.n with
  | Typ_btvar _ 
  | Typ_const _  -> Some t
  | Typ_app(t, _) -> get_tycon t
  | _ -> None

let base_kind = function
  | Kind_type -> true
  | _ -> false

let sortByFieldName (fn_a_l:list<(fieldname * 'a)>) =
  fn_a_l |> List.sortWith
      (fun (fn1, _) (fn2, _) ->
        String.compare
          (text_of_lid fn1)
          (text_of_lid fn2))
    

let kt_kt = Const.kunary ktype ktype
let kt_kt_kt = Const.kbin ktype ktype ktype

let tand = ftv Const.and_lid kt_kt_kt
let tor  = ftv Const.or_lid kt_kt_kt
let timp = ftv Const.imp_lid kt_kt_kt
let tiff = ftv Const.iff_lid kt_kt_kt
let b2t_v = ftv Const.b2t_lid kun

let mk_conj_opt phi1 phi2 = match phi1 with
  | None -> Some phi2
  | Some phi1 -> Some <| mk_Typ_app(tand, [(Inl phi1, false); (Inl phi2, false)]) ktype (Range.union_ranges phi1.pos phi2.pos)
let mk_binop op_t phi1 phi2 = mk_Typ_app(op_t, [(Inl phi1, false); (Inl phi2, false)]) ktype (Range.union_ranges phi1.pos phi2.pos)
let mk_neg phi = mk_Typ_app(ftv Const.not_lid kt_kt, [Inl phi, false]) ktype phi.pos
let mk_conj phi1 phi2 = mk_binop tand phi1 phi2
let mk_conj_l phi = match phi with 
    | [] -> ftv Const.true_lid ktype
    | hd::tl -> List.fold_right mk_conj tl hd
let mk_disj phi1 phi2 = mk_binop tor phi1 phi2
let mk_disj_l phi = match phi with 
    | [] -> ftv Const.false_lid ktype
    | hd::tl -> List.fold_right mk_disj tl hd
let mk_imp phi1 phi2  = mk_binop timp phi1 phi2
let mk_iff phi1 phi2  = mk_binop tiff phi1 phi2
let b2t e = mk_Typ_app(b2t_v, [varg <| e]) kun e.pos//implicitly coerce a boolean to a type     

let eq_k = 
    let a = bvd_to_bvar_s (new_bvd None) ktype in
    let atyp = btvar_to_typ a in
    let b = bvd_to_bvar_s (new_bvd None) ktype in 
    let btyp = btvar_to_typ b in
    mk_Kind_arrow([(Inl a, true); (Inl b, true); null_v_binder atyp; null_v_binder btyp],
                  ktype) dummyRange

let teq = ftv Const.eq2_lid eq_k
let mk_eq e1 e2 = mk_Typ_app(teq, [(Inr e1, false); (Inr e2, false)]) ktype (Range.union_ranges e1.pos e2.pos)

let forall_kind =
  let a = bvd_to_bvar_s (new_bvd None) ktype in
  let atyp = btvar_to_typ a in
  mk_Kind_arrow([(Inl a, true); 
                 null_t_binder <| mk_Kind_arrow([null_v_binder atyp], ktype) dummyRange], 
                ktype) 
                dummyRange
let tforall = ftv Const.forall_lid forall_kind 

let allT_k k = mk_Kind_arrow([null_t_binder <| mk_Kind_arrow([null_t_binder k], ktype) dummyRange], ktype) dummyRange 
let eqT_k k = mk_Kind_arrow([null_t_binder <| k; null_t_binder k], ktype) dummyRange 
   
let tforall_typ k = ftv Const.allTyp_lid (allT_k k)
    
let mk_forallT a b = 
  mk_Typ_app(tforall_typ a.sort, [targ <| mk_Typ_lam([t_binder a], b) (mk_Kind_arrow([null_t_binder a.sort], ktype) dummyRange) dummyRange]) ktype dummyRange

let mk_forall (x:bvvar) (body:typ) : typ =
  let r = dummyRange in
  mk_Typ_app(tforall, [(targ <| mk_Typ_lam([v_binder x], body) (mk_Kind_arrow([null_v_binder x.sort], ktype) r) r)]) ktype r
  
let rec is_wild_pat p =
    match p.v with
    | Pat_wild _ -> true
    | _ -> false

let head_and_args t = 
    let t = compress_typ t in
    match t.n with
        | Typ_app(head, args) -> head, args
        | _ -> t, []

let head_and_args_e e = 
    let e = compress_exp e in 
    match e.n with 
        | Exp_app(head, args) -> head, args
        | _ -> e, []

let function_formals t = 
    let t = compress_typ t in
    match t.n with 
        | Typ_fun(bs, c) -> Some (bs, c)
        | _ -> None

(**************************************************************************************)
(* Destructing a type as a formula *)
(**************************************************************************************)
type qpats = args
type connective = 
    | QAll of binders * qpats * typ
    | QEx of binders * qpats * typ
    | BaseConn of lident * args

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
            let t, args = head_and_args f in 
            if is_constructor t lid 
                && List.length args = List.length arity
                && List.forall2 (fun arg flag -> match arg with 
                | Inl _, _ -> flag=type_sort
                | Inr _, _ -> flag=term_sort) args arity
            then Some <| BaseConn(lid, args)
            else None in
        Util.find_map connectives (aux f) in

    let patterns t = 
        let t = compress_typ t in 
        match t.n with 
            | Typ_meta(Meta_pattern(t, pats)) -> pats, compress_typ t
            | _ -> [], compress_typ t in

    let destruct_q_conn t =
        let is_q : bool -> lident -> Tot<bool> = fun fa l -> if fa then is_forall l else is_exists l in 
        let flat t = 
            let t, args = head_and_args t in 
            t, args |> List.map (function (Inl t, imp) -> Inl <| compress_typ t, imp
                                        | (Inr e, imp) -> Inr <| compress_exp e, imp) in
        let rec aux qopt out t = match qopt, flat t with
            | Some fa, ({n=Typ_const tc}, [(Inl {n=Typ_lam([b], t2)}, _)])  
            | Some fa, ({n=Typ_const tc}, [_; (Inl {n=Typ_lam([b], t2)}, _)])  
                when (is_q fa tc.v) ->
              aux qopt (b::out) t2

            | None, ({n=Typ_const tc}, [(Inl {n=Typ_lam([b], t2)}, _)])  
            | None, ({n=Typ_const tc}, [_; (Inl {n=Typ_lam([b], t2)}, _)])  
                when (is_qlid tc.v) -> 
              aux (Some <| is_forall tc.v) (b::out) t2
            
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
    match c.n with
        | Comp c -> c
        | Total t -> {effect_name=Const.tot_effect_lid; result_typ=t; effect_args=[]; flags=[TOTAL]} 
        


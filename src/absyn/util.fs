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

//let compress_kind = Visit.compress_kind
//let compress_typ  = Visit.compress_typ
//let compress_exp  = Visit.compress_exp 
let force_comp = Visit.compress_comp_typ
let compress_comp = Visit.compress_comp

(********************************************************************************)
(*************************** Delayed substitutions ******************************)
(********************************************************************************)
let bvd_eq bvd1 bvd2 = bvd1.realname.idText=bvd2.realname.idText
let subst_to_string s = 
  s |> List.map (function Inl (b, _) -> b.realname.idText | Inr (x, _) -> x.realname.idText) |> String.concat ", "

(* delayed substitutions *)
let subst_tvar s t = match t.t with 
  | Typ_btvar a -> 
    begin match Util.find_opt (function Inl (b, _) -> bvd_eq b a.v | _ -> false) s with 
      | Some (Inl(_, t)) -> t
      | _ -> t
    end
  | _ -> failwith "impossible"
let subst_xvar s e = match e with
  | Exp_bvar x -> 
    begin match Util.find_opt (function Inr(y, _) -> bvd_eq y x.v | _ -> false) s with
            | Some (Inr(_, e)) -> e
            | _ -> e
    end
  | _ -> failwith "impossible"
let rec subst_typ s t = match s with 
  | [] -> t
  | _ -> match Visit.compress_typ t with 
    | {t=Typ_delayed(t', s', m)} -> withkind t.k <| Typ_delayed(t', compose_subst s' s, Util.mk_ref None) //m is ref None
    | t -> match t.t with 
      | Typ_btvar a -> 
      //  printfn "Trying to subst. %s with [%s]\n" (a.v.realname.idText) (subst_to_string s);
        subst_tvar s t
      | _ -> withkind t.k <| Typ_delayed(t, s, Util.mk_ref None)

and subst_exp s e = match s with 
  | [] -> e
  | _ -> match Visit.compress_exp e with 
    | Exp_delayed(e, s',m) -> Exp_delayed(e, compose_subst s' s, Util.mk_ref None)
    | e -> 
      match e with 
        | Exp_bvar _ -> subst_xvar s e
        | _ -> Exp_delayed(e, s, Util.mk_ref None)

and subst_kind s k = match s with 
  | [] -> k 
  | _ -> 
  let k = Visit.compress_kind k in
    match k with
    | Kind_type
    | Kind_effect
    | Kind_unknown -> k
    | Kind_delayed(k, s',m) -> Kind_delayed(k, compose_subst s' s, Util.mk_ref None)
    | k -> Kind_delayed(k, s, Util.mk_ref None)

and subst_comp_typ s t = match s with 
  | [] -> t
  | _ -> 
    {t with result_typ=subst_typ s t.result_typ; 
            effect_args=List.map (function Inl t -> Inl <| subst_typ s t | Inr e -> Inr <| subst_exp s e) t.effect_args}
and subst_comp s t = match s with 
  | [] -> t
  | _ -> 
    match compress_comp t with 
      | Total t -> Total (subst_typ s t)
      | Flex(u, t) -> Flex(u, subst_typ s t)
      | Comp ct -> Comp(subst_comp_typ s ct)

and compose_subst (s1:subst) s2 = 
  (s1 |> List.map (function 
      | Inl(x, t) -> Inl (x, subst_typ s2 t)
      | Inr(x, e) -> Inr (x, subst_exp s2 e)))@s2 

let restrict_subst axs s = 
  s |> List.filter (fun b ->
    let r = match b with 
    | Inl(a, _) -> not (axs |> Util.for_some (function Inr _ -> false | Inl b -> bvd_eq a b))
    | Inr(x, _) -> not (axs |> Util.for_some (function Inl _ -> false | Inr y -> bvd_eq x y)) in
    //if not r then printfn "Filtering %s\n" (match b with Inl (b, _) -> b.realname.idText | Inr (x, _) -> x.realname.idText);
    r)

let rec map_knd s vk mt me descend binders k = 
  subst_kind (restrict_subst binders s) k, descend
and map_typ s mk vt me descend binders t = 
  subst_typ (restrict_subst binders s) t, descend
and map_exp s mk me ve descend binders e =
  subst_exp (restrict_subst binders s) e, descend
and visit_knd s vk mt me descend binders k = 
  let k = Visit.compress_kind k in 
  if descend 
  then let k, _ = vk false binders k in k, descend
  else map_knd s vk mt me descend binders k
and visit_typ s mk vt me descend binders t = 
  let t = Visit.compress_typ t in
  match t.t with
    | Typ_btvar a -> 
      //printfn "Trying to subst. %s with [%s]\n" (a.v.realname.idText) (s |> subst_to_string);
      compress_typ' <| subst_tvar (restrict_subst binders s) t, descend
    | _ when (not descend) -> map_typ s mk vt me descend binders t
    | _ -> let t, _ = vt false binders t in t, descend
and visit_exp s mk me ve descend binders e =
  let e = Visit.compress_exp e in 
  match e with 
    | Exp_bvar _ ->   compress_exp' <| subst_xvar (restrict_subst binders s) e, descend
    | _ when (not descend) -> map_exp s mk me ve descend binders e
    | _ -> let e, _ = ve false binders e in e, descend
and compress_kind' k = match Visit.compress_kind k with 
  | Kind_delayed (k',s, m) ->
    let k' = fst <| Visit.reduce_kind (visit_knd s) (map_typ s) (map_exp s) Visit.combine_kind Visit.combine_typ Visit.combine_exp true [] k' in
    m := Some k'; 
    k'
  | k -> k
and compress_typ' t = match Visit.compress_typ t with 
  | {t=Typ_delayed (t', s, m)} ->
    let res = fst <| Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) Visit.combine_kind Visit.combine_typ Visit.combine_exp true [] t' in
    m := Some res;
    //printfn "Compressing %A ... got %A\n" t' res;
    res
  | t -> t
and compress_exp' e = match Visit.compress_exp e with 
  | Exp_delayed (e',s, m) ->
    let e = fst <| Visit.reduce_exp (map_knd s) (map_typ s) (visit_exp s) Visit.combine_kind Visit.combine_typ Visit.combine_exp true [] e' in
    m := Some e;
    e
  | e -> e

let compress_kind k = 
  let t = compress_kind' k in
  match t with 
    | Kind_delayed _ -> failwith "Compressed kind but still delayed"
    | _ -> t
 
let compress_typ t = 
  let t = compress_typ' t in
  match t with 
    | {t=Typ_delayed _ } -> failwith "Compressed typ but still delayed"
    | _ -> t

let compress_exp t = 
  let t = compress_exp' t in
  match t with 
    | Exp_delayed _ -> failwith "Compressed exp but still delayed"
    | _ -> t

(********************************************************************************)
(**************************Utilities for identifiers ****************************)
(********************************************************************************)
let mk_discriminator lid = 
  lid_of_ids (lid.ns@[Syntax.mk_ident("is_" ^ lid.ident.idText, lid.ident.idRange)])

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

let is_name (lid:lident) = 
  let c = Util.char_at lid.ident.idText 0 in
  Util.is_upper c

let range_of_bvd x = x.ppname.idRange
let mkbvd (x,y) = {ppname=x;realname=y;instantiation=mk_ref None}
let setsort w t = {v=w.v; sort=t; p=w.p}
let withinfo e s r = {v=e; sort=s; p=r}
let withsort e s   = withinfo e s dummyRange
let bvar_ppname bv = bv.v.ppname 
let bvar_realname bv = bv.v.realname
let bvar_eq (bv1:bvar<'a,'b>) (bv2:bvar<'a,'b>) = 
  (bvar_realname bv1).idText = (bvar_realname bv2).idText
let lbname_eq l1 l2 = match l1, l2 with
  | Inl x, Inl y -> bvd_eq x y
  | Inr l, Inr m -> lid_equals l m
  | _ -> false
let fvar_eq fv1 fv2  = lid_equals fv1.v fv2.v
let bvd_to_bvar_s bvd sort = {v=bvd; sort=sort; p=bvd.ppname.idRange}
let bvar_to_bvd bv = bv.v
let btvar_to_typ bv  = withkind kun <| Typ_btvar bv
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
let fv l = withinfo l tun (range_of_lid l)
let fvar l r = Exp_fvar(fv (set_lid_range l r), false)
let ftv l = withkind kun <| Typ_const (withinfo l Kind_unknown (range_of_lid l))
let order_bvd x y = match x, y with 
  | Inl _, Inr _ -> -1
  | Inr _, Inl _ -> 1
  | Inl x, Inl y -> String.compare x.ppname.idText y.ppname.idText
  | Inr x, Inr y -> String.compare x.ppname.idText y.ppname.idText

let ml_comp t r =  
  Comp ({effect_name=set_lid_range Const.ml_effect_lid r;
         result_typ=t;
         effect_args=[];
         flags=[MLEFFECT]})
    
let total_comp t r = Total t

let comp_flags c = match compress_comp c with 
  | Total _ -> [TOTAL]
  | Comp ct -> ct.flags
  | Flex _ -> []

let is_total_comp c = List.contains TOTAL (comp_flags c)

let is_ml_comp = function
  | Comp c -> lid_equals c.effect_name Const.ml_effect_lid || List.contains MLEFFECT c.flags
  | _ -> false

let comp_result c = match compress_comp c with 
  | Total t
  | Flex (_, t) -> t
  | Comp ct -> ct.result_typ

let is_trivial_wp c = 
  let f = comp_flags c in
  List.contains TOTAL f || List.contains RETURN f

(********************************************************************************)
(****************Simple utils on the local structure of a term ******************)
(********************************************************************************)

let rec ascribe e t = match e with 
  | Exp_ascribed (e, _) -> ascribe e t
  | _ -> withsort (Exp_ascribed(e, t)) t
    
let rec unascribe e = match e with 
  | Exp_ascribed (e, _) -> unascribe e 
  | _ -> e

let rec ascribe_typ t k = match t.t with 
  |  Typ_ascribed (t', _) -> ascribe_typ t' k
  | _ -> Typ_ascribed(t, k)
    
let rec unascribe_typ t = match t.t with 
  | Typ_ascribed (t, _)  
  | Typ_meta(Meta_pos(t, _)) -> unascribe_typ t
  | _ -> t

let rec unrefine t = match t.t with 
  | Typ_refine(x, t, _) -> unrefine t
  | _ -> t

let pos e r' = match e with 
  | Exp_meta(Meta_info(_, _, r)) -> r
  | Exp_bvar x -> x.v.ppname.idRange
  | Exp_fvar(l, _) -> range_of_lid l.v
  | _ -> r'

let tpos t = match t.t with  
  | Typ_meta (Meta_pos(t, r)) -> r
  | Typ_btvar btv -> btv.v.ppname.idRange
  | Typ_const l -> range_of_lid l.v
  | _ -> failwith "Missing position info"


let rec pre_typ t = match (compress_typ t).t with 
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
      | _              -> compress_typ t, acc in
  (fun t -> aux [] t)

let destruct typ lid = 
  match flatten_typ_apps typ with 
    | {t=Typ_const tc}, args when lid_equals tc.v lid -> Some args
    | _ -> None

let rec lids_of_sigelt se = match se with 
  | Sig_bundle(ses, _) -> List.collect lids_of_sigelt ses
  | Sig_tycon (lid, _, _,  _, _, _, _)    
  | Sig_typ_abbrev  (lid, _, _, _, _, _)
  | Sig_datacon (lid, _, _, _)
  | Sig_val_decl (lid, _, _, _, _) 
  | Sig_assume (lid, _, _, _, _)
  | Sig_logic_function (lid, _, _, _) -> [lid]
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
  | Sig_datacon (_, _, _, r)
  | Sig_val_decl (_, _, _, _, r) 
  | Sig_assume (_, _, _, _, r)
  | Sig_logic_function (_, _, _, r) 
  | Sig_let(_, r) 
  | Sig_main(_, r) 
  | Sig_monads(_, _, r) -> r

let range_of_exp e def = match e with 
  | Exp_meta(Meta_info(_, _, p)) -> p
  | Exp_bvar x -> range_of_bvd x.v
  | Exp_fvar (l, _) -> range_of_lid l.v
  | _ -> def

let opt_range_of_exp e  = match e with 
  | Exp_meta(Meta_info(_, _, p)) -> Some p
  | Exp_bvar x -> Some <| range_of_bvd x.v
  | Exp_fvar (l, _) -> Some <| range_of_lid l.v
  | _ -> None

let range_of_typ t def = match t.t with 
  | Typ_meta(Meta_pos(_, r)) -> r
  | Typ_meta(Meta_named(_, l)) -> range_of_lid l
  | _ -> def

let opt_range_of_typ t = match t.t with 
  | Typ_meta(Meta_pos(_, r)) -> Some r
  | Typ_meta(Meta_named(_, l)) -> Some <| range_of_lid l
  | _ -> None

let set_range_of_typ t r = match t.t with 
  | Typ_meta(Meta_pos(t', _)) -> withkind t.k <| Typ_meta(Meta_pos(t', r))
  | _ -> withkind t.k <| Typ_meta(Meta_pos(t, r))

let range_of_lb = function
  | (Inl x, _, _) -> range_of_bvd x
  | (Inr l, _, _) -> range_of_lid l 

let mk_curried_app e e_or_t = 
  List.fold_left (fun f -> function
    | Inl t -> Exp_tapp(f, t) 
    | Inr (e, imp) -> Exp_app(f, e, imp))  e e_or_t 

let mk_typ_app f args = 
  List.fold_left (fun f -> function
    | Inl t -> withkind kun <| Typ_app(f, t, false) 
    | Inr e -> withkind kun <| Typ_dep(f, e, false)) f args

let uncurry_app e =
  let rec aux e out = match e with 
    | Exp_meta(Meta_info(e, _, _)) -> aux e out
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
(************** Collecting all unification variables in a type ******************)
(********************************************************************************)

type uvars = {
  uvars_k: list<uvar_k>;
  uvars_t: list<(uvar_t*knd)>;
  uvars_e: list<(uvar_e*typ)>
  }
let empty_uvars = {uvars_k=[]; uvars_t=[]; uvars_e=[]}
let collect_uvars_k uvs k = match k with 
  | Kind_uvar uv -> 
      (match List.tryFind (Unionfind.equivalent uv) uvs.uvars_k with 
          | Some _ -> uvs, k
          | None -> {uvs with uvars_k=uv::uvs.uvars_k}, k)
  | Kind_delayed _ -> uvs, compress_kind k
  | _ -> uvs, k
let collect_uvars_t uvs t : uvars * typ = match t.t with 
    | Typ_uvar (uv, k) -> 
        (match List.tryFind (fun (uv', _) -> Unionfind.equivalent uv uv') uvs.uvars_t with 
          | Some _ -> uvs, t
          | None -> {uvs with uvars_t=(uv,k)::uvs.uvars_t}, t)
    | Typ_delayed _ -> uvs, compress_typ t
    | _ -> uvs, t 

let collect_uvars_e uvs e : uvars * exp = match e with 
    | Exp_uvar (uv, t) -> 
        (match List.tryFind (fun (uv', _) -> Unionfind.equivalent uv uv') uvs.uvars_e with 
          | Some _ -> uvs, e
          | None -> {uvs with uvars_e=(uv,t)::uvs.uvars_e}, e)
    | Exp_delayed _ -> uvs, compress_exp e
    | _ -> uvs, e 
let uvars_in_kind k : uvars = 
  fst <| Visit.visit_kind_simple false collect_uvars_k collect_uvars_t collect_uvars_e empty_uvars k
let uvars_in_typ t : uvars = 
  fst <| Visit.visit_typ_simple false collect_uvars_k collect_uvars_t collect_uvars_e empty_uvars t
let uvars_in_exp e : uvars = 
  fst <| Visit.visit_exp_simple false collect_uvars_k collect_uvars_t collect_uvars_e empty_uvars e
let uvars_in_typ' t : uvars = 
  fst <| Visit.visit_typ_simple true collect_uvars_k collect_uvars_t collect_uvars_e empty_uvars t
let unchecked_unify uv t = 
  match Unionfind.find uv with 
    | Fixed _ -> failwith "Changing a fixed uvar!"
    | _ -> Unionfind.change uv (Fixed t) (* used to be an alpha-convert t here *)


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
  match t.t with
    | Typ_btvar bv -> 
      if is_bound_tv benv bv then out, t
      else if !Options.fvdie then failwith (Util.format1 "Freevar : %s\n" (bv.v.realname.idText))
      else (add_unique bvar_eq bv ftvs, fxvs), t
    | Typ_delayed _ -> 
      out, compress_typ t
    | _ -> out, t 
let fv_fold_e (out:freevars) (benv:boundvars) (e:exp) : (freevars * exp) =
  let (ftvs, fxvs) = out in
  match e with
    | Exp_bvar bv ->
      if is_bound_xv benv bv then out, e (* let _ = pr "Bvar %s is bound, where env is %s\n" (strBvar bv) (strBenv benv) in *)
      else (ftvs, add_unique bvar_eq bv fxvs), e      (* let _ = pr "Bvar %s is free, where env is %s\n" (strBvar bv) (strBenv benv) in *)
    | Exp_delayed _ -> 
      out, compress_exp e
    | _ -> out, e 
let ext_fv_env ((btvs, bxvs):boundvars) : either<btvar,bvvar> -> (boundvars * either<btvdef, bvvdef>) =
  function 
    | Inl tv -> (tv.v::btvs, bxvs), Inl tv.v
    | Inr xv -> (btvs, xv.v::bxvs), Inr xv.v 
let fold_kind_noop env benv k = match k with 
  | Kind_delayed _ -> (env, compress_kind k)
  | _ -> (env, k)

let freevars_kind : knd -> freevars = 
  fun k -> fst <| Visit.visit_kind true fold_kind_noop fv_fold_t fv_fold_e (fun _ e -> e) ext_fv_env ([], []) ([], []) k
      
let freevars_typ : typ -> freevars = 
  fun t -> fst <| Visit.visit_typ true fold_kind_noop fv_fold_t fv_fold_e (fun _ e -> e) ext_fv_env ([], []) ([], []) t
      
let freevars_exp : exp -> freevars =
  fun e -> fst <| Visit.visit_exp true fold_kind_noop fv_fold_t fv_fold_e (fun _ e -> e) ext_fv_env ([], []) ([], []) e

let freevars_comp_typ : comp_typ -> freevars = 
  fun c -> 
    let t = withkind kun <| Typ_app(ftv c.effect_name, c.result_typ, false) in
    freevars_typ <| mk_typ_app t c.effect_args

let freevars_comp c = match compress_comp c with 
  | Total t
  | Flex(_, t) -> freevars_typ t
  | Comp ct -> freevars_comp_typ ct

let is_free axs (fvs:freevars) = 
  axs |> Util.for_some (function 
    | Inl a -> fst fvs |> Util.for_some (fun b -> bvd_eq a b.v)
    | Inr x -> snd fvs |> Util.for_some (fun y -> bvd_eq x y.v))
  
(********************************************************************************)
(************************** Type/term substitutions *****************************)
(********************************************************************************)

(* Eager substitutions *)
let mk_subst_map (s:subst) = 
  let t = Util.smap_create(List.length s) in
  s |> List.iter (function 
    | Inl(a, ty) -> Util.smap_add t a.realname.idText (Inl ty)
    | Inr(x, e) -> Util.smap_add t x.realname.idText (Inr e));
  t
let lift_subst f = (fun () x -> (), f x)
(* Should never call these ones directly *)
let rec eager_subst_kind' (s:subst_map) (k:knd) : knd =
  snd (Visit.visit_kind_simple true
         (fun e k -> e,k)
         (lift_subst (eager_subst_tvar s))
         (lift_subst (eager_subst_xvar s))
         () k)
and eager_subst_typ' (s:subst_map) (t:typ) : typ =
  snd (Visit.visit_typ_simple true
         (fun e k -> e,k)
         (lift_subst (eager_subst_tvar s))
         (lift_subst (eager_subst_xvar s))
         () t)
and eager_subst_exp' (s:subst_map) (e:exp) : exp =
  snd (Visit.visit_exp_simple true
         (fun e k -> e,k)
         (lift_subst (eager_subst_tvar s))
         (lift_subst (eager_subst_xvar s))
         () e)
and eager_subst_tvar (s:subst_map) (t:typ) : typ =
  let find_typ btv = match Util.smap_try_find s btv.realname.idText with 
    | Some (Inl l) -> Some l
    | _ ->  None in
  match t.t with
    | Typ_btvar btv ->
      begin
        match find_typ btv.v with
          | Some t -> t
          | _ -> t
      end
    | Typ_delayed _ -> compress_typ t
    | _ -> t
and eager_subst_xvar (s:subst_map) (e:exp) : exp =
  let find_exp bv =  match Util.smap_try_find s bv.realname.idText with 
    | Some (Inr e) -> Some e
    | _ ->  None in
  match e with
    | Exp_bvar bv ->
      begin
        match find_exp bv.v with
          | Some e -> e
          | None -> e
      end
    | Exp_delayed _ -> compress_exp e
    | _ -> e

let eager_subst_kind s k = match s with 
  | [] -> k
  | _ -> eager_subst_kind' (mk_subst_map s) k 
let eager_subst_typ s t = match s with 
  | [] -> t
  | _ -> eager_subst_typ' (mk_subst_map s) t
let eager_subst_exp s e = match s with
  | [] -> e
  | _ -> eager_subst_exp' (mk_subst_map s) e 
let eager_subst_comp_typ s t = match s with 
  | [] -> t
  | _ -> 
    {t with result_typ=eager_subst_typ s t.result_typ; 
            effect_args=List.map (function Inl t -> Inl <| eager_subst_typ s t | Inr e -> Inr <| eager_subst_exp s e) t.effect_args}
let eager_subst_comp s t = match s with 
  | [] -> t
  | _ -> 
    match compress_comp t with 
      | Total t -> Total (eager_subst_typ s t)
      | Flex(u, t) -> Flex(u, eager_subst_typ s t)
      | Comp ct -> Comp(eager_subst_comp_typ s ct)

(***********************************************************************************************)
(* closing types and terms *)
(***********************************************************************************************)
let close_with_lam tps t = List.fold_right
  (fun tp out -> match tp with
    | Tparam_typ (a,k) -> withkind (Kind_tcon(Some a, k, out.k, false)) <| Typ_tlam (a,k,out)
    | Tparam_term (x,t) -> withkind (Kind_dcon(Some x, t, out.k, false)) <| Typ_lam (x,t,out))
  tps t 

let close_with_arrow tps t =
  t |> (tps |> List.fold_right (
    fun tp out -> match tp with
      | Tparam_typ (a,k) -> withkind Kind_type <| Typ_univ (a,k, total_comp out (range_of_bvd a))
      | Tparam_term (x,t) -> withkind Kind_type <| Typ_fun (Some x,t, total_comp out (range_of_bvd x), true)))

let close_typ = close_with_arrow
      
let close_kind tps k = 
    List.fold_right 
        (fun tp k -> match tp with
            | Tparam_typ (a, k') -> Kind_tcon(Some a, k', k, false)
            | Tparam_term (x, t) -> Kind_dcon(Some x, t, k, false))
        tps k 

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

let freshen_bvars_typ (ropt:option<Range.range>) (t:typ) subst : typ =
  snd (Visit.visit_typ true
         fold_kind_noop
         (fun () subst t -> (), eager_subst_tvar (mk_subst_map subst) t)
         (fun () subst e -> (), eager_subst_xvar (mk_subst_map subst) e)
         (freshen_label ropt)
         ext () subst t) 

let freshen_bvars_kind (ropt:option<Range.range>) (k:knd) subst : knd =
  snd (Visit.visit_kind true
         fold_kind_noop
         (fun () subst t -> (), eager_subst_tvar (mk_subst_map subst) t)
         (fun () subst e -> (), eager_subst_xvar (mk_subst_map subst) e)
         (freshen_label ropt)
         ext () subst k)

(* move to de Bruijn? *)
//let freshen_typ t benv   : typ  = freshen_bvars_typ None t benv
let alpha_convert t      : typ  = freshen_bvars_typ None t []
//let alpha_convert_kind k : knd = freshen_bvars_kind None k []
//let alpha_fresh_labels r t : typ = freshen_bvars_typ (Some r) t []


(********************************************************************************)
(******************** Reducing to weak head normal form *************************)
(***********************(inefficient--see Krivine.fs)****************************)

let whnf t =
  let rec aux ctr t =
    let t' = match (compress_typ t).t with
      | Typ_dep(t1, e, imp) ->
        let t1,ctr = aux (ctr+1) t1 in
        (match t1.t with
          | Typ_lam(x, t1_a, t1_r) ->
            let t1_r' = subst_typ [Inr(x,e)] t1_r in
            aux (ctr+1) t1_r'
          | _ -> withkind t.k <| Typ_dep(t1, e, imp), ctr)
      | Typ_app(t1, t2, imp) ->
        let t1,ctr = aux (ctr+1) t1 in
        let t2,ctr = aux (ctr+1) t2 in
        (match t1.t with
          | Typ_tlam(a, t1_a, t1_r) ->
            let t1_r' = subst_typ [Inl(a,t2)] t1_r in
            aux (ctr+1) t1_r'
          | _ -> withkind t.k <| Typ_app(t1, t2, imp), ctr)
      | t' -> withkind t.k t', ctr in
    t' in
  fst (aux 0 t)

(********************************************************************************)
(*********************** Various tests on constants  ****************************)
(********************************************************************************)
let is_tuple_constructor (t:typ) = match t.t with 
  | Typ_const l -> Util.starts_with l.v.str "Prims.Tuple"
  | _ -> false

let mk_tuple_lid n r = 
  let t = Util.format1 "Tuple%s" (Util.string_of_int n) in
  set_lid_range (Const.pconst t) r

let mk_tuple_data_lid n r = 
  let t = Util.format1 "MkTuple%s" (Util.string_of_int n) in
  set_lid_range (Const.pconst t) r

let is_dtuple_constructor (t:typ) = match t.t with 
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

let is_forall lid = lid_equals lid Const.forall_lid
let is_exists lid = lid_equals lid Const.exists_lid
let is_qlid lid   = is_forall lid || is_exists lid
let is_equality x = is_lid_equality x.v

let lid_is_connective =
  let lst = [Const.and_lid; Const.or_lid; Const.not_lid;
             Const.iff_lid; Const.imp_lid] in
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

let rec is_function_typ t = 
  match (compress_typ t).t with 
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
  | None ->  Typ_lam(new_bvd None, t1, t2)
  | Some x-> Typ_lam(x, t1, t2)

let mkRefinedUnit formula =
  let bvd = new_bvd None in
  let t = Typ_refine(bvd, ftv Const.unit_lid, formula) in
  t, bvd.realname

let findValDecl (vds:list<sigelt>) bvd : option<sigelt> =
  vds |> Util.find_opt (function
                         | Sig_val_decl(lid, t, _, _, _) -> lid.ident.idText = bvd.ppname.idText
                         | _ -> false)
      
let rec typs_of_letbinding x = match x with
  | (_, t, e)::tl -> t::typs_of_letbinding tl
  | _ -> []

let mk_conj_opt phi1 phi2 = match phi1 with
  | None -> Some phi2
  | Some phi1 ->
    let app1 = withkind kun <| Typ_app(ftv Const.and_lid, phi1, false) in
    let and_t = withkind kun <| Typ_app(app1, phi2, false) in
    Some and_t

let mk_binop op phi1 phi2 = 
  let app1 = withkind (Kind_tcon(None, Kind_type, Kind_type, false)) <| Typ_app(ftv op, phi1, false) in
  withkind Kind_type <| Typ_app(app1, phi2, false)

let mk_neg phi = withkind Kind_type <| Typ_app(ftv Const.not_lid, phi, false)
let mk_conj phi1 phi2 = mk_binop Const.and_lid phi1 phi2
let mk_disj phi1 phi2 = mk_binop Const.or_lid phi1 phi2
let mk_imp phi1 phi2  = mk_binop Const.imp_lid phi1 phi2
let mk_iff phi1 phi2  = mk_binop Const.iff_lid phi1 phi2
let mk_eq e1 e2       = 
  let app1 = withkind kun <| Typ_dep(ftv Const.eq2_lid, e1, false) in
  withkind Kind_type <| Typ_dep(app1, e2, false)

let normalizeRefinement t =
  let rec aux xopt t = match t.t with
    | Typ_refine(bvd, t', phi) ->
      let x, phi = match xopt with
        | None ->
          Some (bvd_to_exp bvd t'), phi
        | Some x ->
          xopt, subst_typ [Inr(bvd,x)] phi in
      let t', phi_opt = aux xopt t' in
      t', mk_conj_opt phi_opt phi
    | _ -> t, None in
  aux None t
 
let forall_kind =
  let a = new_bvd None in
  let atyp = bvd_to_typ a Kind_type in
    Kind_tcon(Some a, Kind_type,
              Kind_tcon(None, Kind_dcon(None, atyp, Kind_type, false),
                        Kind_type, 
                        false), 
              true)

let mk_forallT a k b = match k with 
  | Kind_type -> 
    let allT_k = Kind_tcon(None, Kind_tcon(Some a, Kind_type, Kind_type, false), Kind_type, false) in 
    let forall_typ = withkind allT_k <| Typ_const(withsort Const.allTyp_lid allT_k) in
    withkind Kind_type <| Typ_app(forall_typ, b, false) 
  | _ -> failwith "NYI"

let mk_forall (x:bvvdef) (a:typ) (body:typ) : typ =
  let forall_typ = withkind kun <| Typ_const(withsort Const.forall_lid forall_kind) in
  withkind kun <| Typ_app(withkind kun <| Typ_app(forall_typ, a, true), withkind kun <| Typ_lam(x, a, body), false)
  
let un_forall t = match t.t with
  | Typ_app({t=Typ_app({t=Typ_const(lid)}, _, _)}, 
            {t=Typ_lam(x, t, body)}, _) when is_forall lid.v ->
    Some (x, t, body)
  | _ -> None

(* collect all curried arguments until we reach a non-trivial computation type *)
let collect_formals t = 
  let rec aux out t =
      match (whnf t).t with
        | Typ_fun(xopt, t1, cod, imp) -> 
          let out = Inr(xopt,t1,imp)::out in
          begin match compress_comp cod with 
            | Total t -> aux out t
            | _ -> List.rev out, cod
          end
        | Typ_univ(a, k, cod) -> 
          let out = Inl(a,k)::out in
          begin match compress_comp cod with 
            | Total t -> aux out t
            | _ -> List.rev out, cod
          end
        | _ -> List.rev out, Total t 
  in aux [] t

let collect_u_quants t =
  let rec aux out t =
    match flatten_typ_apps (whnf t) with
      | {t=Typ_const tc}, [Inl t1; Inl ({t=Typ_lam(x, _, t2)})]
        when is_forall tc.v ->
        aux ((x, t1)::out) t2
      | _ -> List.rev out, t
  in aux [] t

let collect_forall_xt t =
  let rec aux out t =
    match flatten_typ_apps (whnf t) with
      | {t=Typ_const tc}, [Inl t1; Inl ({t=Typ_lam(x, _, t2)})]
        when is_forall tc.v ->
        aux (Inr(x, t1)::out) t2
      | {t=Typ_const tc}, [Inl ({t=Typ_tlam(a, k, t2)})]
          when (lid_equals tc.v Const.allTyp_lid) ->
          aux (Inl(a,k)::out) t2
      | _ -> List.rev out, t
  in aux [] t

let collect_exists_xt t =
  let rec aux out t =
      match flatten_typ_apps (whnf t) with
        | {t=Typ_const tc}, [Inl t1; Inl ({t=Typ_lam(x, _, t2)})]
          when lid_equals tc.v Const.exists_lid ->
          aux (Inr(x, t1)::out) t2
        | {t=Typ_const tc}, [Inl ({t=Typ_tlam(a, k, t2)})]
          when (lid_equals tc.v Const.exTyp_lid) ->
          aux (Inl(a,k)::out) t2
        | _ -> List.rev out, t
  in aux [] t
  
let collect_e_quants t =
  let rec aux out t =
      match flatten_typ_apps (whnf t) with
        | {t=Typ_const tc}, [Inl t1; Inl ({t=Typ_lam(x, _, t2)})]
          when lid_equals tc.v Const.exists_lid ->
          aux ((x, t1)::out) t2
        | _ -> List.rev out, t
  in aux [] t

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

let rec is_wild_pat p =
    match p with
    | Pat_wild -> true
    | Pat_withinfo (p, _) -> is_wild_pat p
    | _ -> false



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
module Microsoft.FStar.Absyn.Visit

open Microsoft.FStar
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Util
open Microsoft.FStar.Profiling

let log s = ()(* if !Options.fvdie then printfn "%d;" s *)

let rec compress_typ_aux pos typ = match typ.n with
  | Typ_uvar (uv,k) -> 
      begin
        match Unionfind.find uv with 
          | Fixed typ -> compress_typ_aux pos typ
          | _ -> typ
      end
  | Typ_delayed(_, _, m) -> 
    (match !m with 
      | None -> typ
      | Some t -> let t' = compress_typ_aux pos t in m := Some t'; t')
  | Typ_ascribed(t, _)
  | Typ_meta(Meta_named(t, _)) when pos -> compress_typ_aux pos t
  | Typ_meta(Meta_uvar_t_app(t, (uv,_))) ->
       begin 
          match Unionfind.find uv with 
            | Fixed t' -> 
              let rec rebuild t = match t.n with 
                | Typ_app(t0, t, imp) -> mk_Typ_app (rebuild t0, t, imp) t.tk t.pos
                | Typ_dep(t0, e, imp) -> mk_Typ_dep (rebuild t0, e, imp) t.tk t.pos
                | _ -> t' in
              rebuild t       
            | _ -> typ
       end
  | _ -> typ
let compress_typ typ = compress_typ_aux true typ
let compress_typ_uvars typ = compress_typ_aux false typ

let rec compress_exp_aux meta exp = match exp.n with 
  | Exp_uvar (uv, _) -> 
    begin
      match Unionfind.find uv with 
        | Fixed e -> compress_exp_aux meta e 
        | _ -> exp
    end
  | Exp_delayed(_, _, m) -> 
    (match !m with 
      | None -> exp
      | Some e -> let e' = compress_exp_aux meta e in m := Some e'; e')
  | Exp_ascribed(e, _)
  | Exp_meta(Meta_desugared(e, _)) when meta -> compress_exp_aux meta e
  | Exp_meta(Meta_uvar_e_app(e, (uv,_))) 
  | Exp_meta(Meta_uvar_e_app(e, (uv,_))) ->
       begin 
          match Unionfind.find uv with 
            | Fixed e' -> 
              let rec rebuild e = match e.n with 
                | Exp_tapp(e0, t) -> mk_Exp_tapp (rebuild e0, t) e.tk e.pos
                | Exp_app(e0, e, imp) -> mk_Exp_app (rebuild e0, e, imp) e.tk e.pos
                | _ -> e' in
              rebuild e      
            | _ -> exp
       end
  | _ -> exp
let compress_exp e = compress_exp_aux true e
let compress_exp_uvars e = compress_exp_aux false e
 
let rec compress_kind knd = match knd.n with 
  | Kind_uvar (uv, _) -> 
    begin
      match Unionfind.find uv with 
        | Fixed k -> compress_kind k
        | _ -> knd
    end
  | Kind_delayed(_, _, m) -> 
    (match !m with 
      | None -> knd
      | Some k -> let k' = compress_kind k in m := Some k'; k')
  | _ -> knd

let rec compress_comp c : comp = match c.n with 
  | Comp _ 
  | Total _ 
  | Rigid _ -> c
  | Flex ({n=Typ_meta(Meta_uvar_t_app(_, (u,_)))}, res_t) -> 
    begin match Unionfind.find u with 
      | Fixed t -> mk_Rigid (mk_Typ_app(t, res_t, false) mk_Kind_effect c.pos) 
      | _ -> c
    end
  | Flex _ -> failwith "Impossible: Flex computation non-pattern"
      
let left ext benv btv = match ext benv (Inl btv) with 
  | benv, Inl bvd -> benv, bvd
  | _ -> failwith "impossible" 
let right ext benv bvv = match ext benv (Inr bvv) with 
  | benv, Inr bvd -> benv, bvd
  | _ -> failwith "impossible" 

(*************************************************************************************)
(* A general way of reducing types. *)
(*************************************************************************************)
type binders = list<either<btvdef, bvvdef>>
type mapper<'env, 'm, 'n> =
    ('env -> binders -> knd -> (knd * 'env))
    -> ('env -> binders -> typ -> (typ * 'env))
    -> ('env -> binders -> exp -> (exp * 'env))
    -> 'env -> binders -> 'm -> ('n * 'env)

let push_tbinder binders = function 
  | None -> binders
  | Some a -> (Inl a)::binders
let push_vbinder binders = function 
  | None -> binders
  | Some a -> (Inr a)::binders

let rec reduce_kind 
    (map_kind': mapper<'env, knd, knd>)
    (map_typ': mapper<'env, typ, typ>)
    (map_exp': mapper<'env, exp, exp>)
    (combine_kind: (knd -> (list<knd> * list<typ> * list<exp>) -> 'env -> (knd * 'env)))
    (combine_typ: (typ -> (list<knd> * list<typ> * list<comp> * list<exp>) -> 'env -> (typ * 'env)))
    (combine_exp: (exp -> (list<knd> * list<typ> * list<exp>) -> 'env -> (exp * 'env))) (env:'env) binders k: (knd * 'env) =
  let rec visit_kind env binders k =
    let k = compress_kind k in
    let kl, tl, el, env =   
      match k.n with 
        | Kind_delayed _ -> failwith "Impossible"
        | Kind_uvar _
        | Kind_type 
        | Kind_effect
        | Kind_unknown -> [], [], [], env
        | Kind_abbrev(kabr, k) -> 
          let k, env = map_kind env binders k in
          let env, ts, es = List.fold_left (fun (env, ts, es) te -> match te with 
            | Inl t -> let t, env = map_typ env binders t in (env, t::ts, es)
            | Inr e -> let e, env = map_exp env binders e in (env, ts, e::es)) (env, [], []) (snd kabr) in
          [k], List.rev ts, List.rev es, env
        | Kind_tcon (aopt, k1, k2, _) -> 
          let k1, env = map_kind env binders k1 in
          let k2, env = map_kind env (push_tbinder binders aopt) k2 in
          [k1;k2], [], [], env
        | Kind_dcon (xopt, t, k, _) -> 
          let t, env = map_typ env binders t in
          let k, env = map_kind env (push_vbinder binders xopt) k in
          [k],[t],[],env in
    combine_kind k (kl, tl, el) env 
  and map_kind env binders k = map_kind' visit_kind map_typ map_exp env binders k
  and map_typ env binders t = reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t 
  and map_exp env binders e = reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e
  in
  map_kind env binders k
      
and reduce_typ 
    (map_kind': mapper<'env, knd, knd>)
    (map_typ': mapper<'env, typ, typ>)
    (map_exp': mapper<'env, exp, exp>)
    (combine_kind: (knd -> (list<knd> * list<typ> * list<exp>) -> 'env -> (knd * 'env)))
    (combine_typ: (typ -> (list<knd> * list<typ> * list<comp> * list<exp>) -> 'env -> (typ * 'env)))
    (combine_exp: (exp -> (list<knd> * list<typ> * list<exp>) -> 'env -> (exp * 'env))) (env:'env) binders t : (typ * 'env) =
  let rec map_typs env binders tl = 
    let tl, _, env = List.fold_left (fun (out, binders, env) (xopt, t) ->
        let t, env = map_typ env binders t in
        let binders = push_vbinder binders xopt in 
        t::out, binders, env) ([], binders, env) tl in
    List.rev tl, env 
  and map_comp (env:'env) (binders:list<either<btvdef,bvvdef>>) (c:comp) = 
    let c = compress_comp c in
    match c.n with
    | Rigid t -> 
      let t, env = map_typ env binders t in
      mk_Rigid(t), env    
    | Flex (u, t) -> 
      let u, env = map_typ env binders u in
      let t, env = map_typ env binders t in
      mk_Flex(u, t), env    
    | Total t -> 
      let t, env = map_typ env binders t in
      mk_Total t, env
    | Comp ct ->
      let t, env = map_typ env binders ct.result_typ in
      let env, args = List.fold_left (fun (env, out) -> function
        | Inl t -> 
          let t, env = map_typ env binders t in
          env, Inl t::out
        | Inr e -> 
          let e, env = map_exp env binders e in
          env, Inr e::out) (env, []) ct.effect_args in 
      mk_Comp ({ct with result_typ=t; effect_args=List.rev args}), env 

  and visit_typ env binders t = 
    let kl, tl, cl, el, env = match (compress_typ t).n with 
      | Typ_delayed _ -> failwith "Impossible"
      | Typ_unknown
      | Typ_btvar _   
      | Typ_const _ -> [],[],[],[], env
      | Typ_app(t1, t2, imp) -> 
        let tl, env = map_typs env binders [(None, t1); (None, t2)] in 
        [], tl, [], [], env 
      | Typ_lam(x, t1, t2)
      | Typ_refine(x, t1, t2) -> 
        let tl, env = map_typs env binders [(Some x, t1); (None, t2)] in 
        [], tl, [], [], env 
      | Typ_fun(xopt, t1, t2, imp) -> 
        let t1, env = map_typ env binders t1 in 
        let binders = push_vbinder binders xopt in
        let t2, env = map_comp env binders t2 in 
        [], [t1], [t2], [], env 
      | Typ_univ(a, k, t) -> 
        let k, env = map_kind env binders k in
        let t, env = map_comp env (push_tbinder binders (Some a)) t in
        [k], [], [t], [], env
      | Typ_tlam(a, k, t) ->
        let k, env = map_kind env binders k in
        let t, env = map_typ env (push_tbinder binders (Some a)) t in
        [k], [t], [], [], env
      | Typ_dep(t, e, imp) -> 
        let t, env = map_typ env binders t in
        let e, env = map_exp env binders e in
        [], [t], [], [e], env
      | Typ_ascribed(t,k) ->  
        let t, env = map_typ env binders t in
        let k, env = map_kind env binders k in
        [k], [t], [], [], env
      | Typ_uvar(_, k) -> 
        let k, env = map_kind env binders k in
        [k], [], [], [], env
      | Typ_meta(Meta_comp c) -> 
        let c, env = map_comp env binders c in
        [], [], [c], [], env
      | Typ_meta(Meta_named(t, _)) ->
        let t, env = map_typ env binders t in
        [], [t], [], [], env 
      | Typ_meta(Meta_uvar_t_app(t, _)) -> 
        let e, env = map_typ env binders t in 
        [], [t], [], [], env
      | Typ_meta(Meta_pattern(t,ps)) -> 
        let t,env = map_typ env binders t in 
        let tpats, vpats, env = List.fold_left (fun (tpats, vpats, env) -> function
          | Inl t -> let t, env = map_typ env binders t in (t::tpats, vpats, env)
          | Inr e -> let e, env = map_exp env binders e in (tpats, e::vpats, env)) ([], [], env) ps in 
        [], t::tpats, [], vpats, env in
    combine_typ t (kl, tl, cl, el) env 
  and map_kind env binders k = reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k 
  and map_typ env binders t = map_typ' map_kind visit_typ map_exp env binders t
  and map_exp env binders e = reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e  
  in
  map_typ env binders t
    
and reduce_exp 
    (map_kind': mapper<'env, knd, knd>)
    (map_typ': mapper<'env, typ, typ>)
    (map_exp': mapper<'env, exp, exp>)
    (combine_kind: (knd -> (list<knd> * list<typ> * list<exp>) -> 'env -> (knd * 'env)))
    (combine_typ: (typ -> (list<knd> * list<typ> * list<comp> * list<exp>) -> 'env -> (typ * 'env)))
    (combine_exp: (exp -> (list<knd> * list<typ> * list<exp>) -> 'env -> (exp * 'env))) (env:'env) binders e : (exp * 'env) =
  let rec map_exps env binders el = 
    let el, env = List.fold_left (fun (out, env) e -> 
      let e, env = map_exp env binders e in
      e::out, env) ([], env) el in
    List.rev el, env 
  and map_exps_with_binders env el = 
    let el, env = List.fold_left (fun (out, env) (b,e) -> 
      let e, env = map_exp env b e in
      e::out, env) ([], env) el in
    List.rev el, env 
  and map_branches_with_binders env el = 
    let el, env = List.fold_left (fun (out, env) (b,wopt,e) -> 
      let w, env = match wopt with 
        | None -> None, env
        | Some w -> 
          let w, env = map_exp env b w in 
          Some w, env in
      let e, env = map_exp env b e in
      (w,e)::out, env) ([], env) el in
    List.rev el, env 
  and map_typs env binders tl = 
    let tl, env = List.fold_left (fun (out, env) t -> 
      let t, env = map_typ env binders t in
      t::out, env) ([], env) tl in
    List.rev tl, env 
  and map_either_l (env:'env) binders (tl:list<either<typ,exp>>) : (list<either<typ,exp>> * 'env) = 
    let tl, env = List.fold_left (fun (out, env) t -> 
      match t with 
        | Inl t -> 
          let t, env = map_typ env binders t in
          Inl t::out, env
        | Inr e -> 
          let e, env = map_exp env binders e in
          Inr e::out, env)
      ([], env) tl in
    List.rev tl, env 
  and map_kind env binders k = reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k 
  and map_typ env binders t = reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t 
  and map_exp env binders e = map_exp' map_kind map_typ visit_exp env binders e
  and visit_exp env binders e = 
     let e = compress_exp_uvars e in 
     let kl, tl, el, env = match e.n with 
        | Exp_delayed _
        | Exp_meta(Meta_datainst _) -> failwith "impossible"
        | Exp_meta(Meta_uvar_e_app(e, _))
        | Exp_meta(Meta_desugared(e, _)) -> 
          let e, env = map_exp env binders e in 
          [], [], [e], env
        | Exp_bvar _  
        | Exp_fvar _ 
        | Exp_constant _ -> [], [], [], env
        | Exp_uvar(_, t) ->  
          let t, env = map_typ env binders t in
          [], [t], [], env
        | Exp_abs(x, t, e) -> 
          let tl, env = map_typs env binders [t] in
          let e, env = map_exp env (push_vbinder binders (Some x)) e in
          [], tl, [e], env
        | Exp_tabs(a, k, e) ->
          let k, env = map_kind env binders k in
          let binders = push_tbinder binders (Some a) in
          let e, env = map_exp env binders e in
          [k], [], [e], env
        | Exp_app(e1, e2, _) -> 
          let el, env = map_exps env binders [e1;e2] in
          [], [], el, env 
        | Exp_tapp(e, t) -> 
          let tl, env = map_typs env binders [t] in 
          let e, env = map_exp env binders e in
          [], tl, [e], env
        | Exp_match(e1, pl) -> 
          let rec pat_binders b p = match p with 
            | Pat_wild
            | Pat_twild
            | Pat_constant _ -> b
            | Pat_withinfo(p, _) -> pat_binders b p
            | Pat_var x -> push_vbinder b (Some x)
            | Pat_tvar t -> push_tbinder b (Some t)
            | Pat_cons(c, pats) -> List.fold_left pat_binders b pats
            | Pat_disj(p::_) -> pat_binders b p
            | Pat_disj [] -> failwith "impossible" in
          let branches = pl |> List.collect (fun (p,w,e) -> 
            let binders = pat_binders binders p in 
            match w with 
              | None -> [(binders, e)]
              | Some w -> [(binders, w); (binders, e)]) in
          let el, env = map_exps_with_binders env ((binders, e1)::branches) in
          [], [], el, env 
        | Exp_ascribed(e, t) ->
          let t, env = map_typ env binders t in
          let e, env = map_exp env binders e in
          [], [t], [e], env
        | Exp_let((false, [(x,t,e1)]), e2) -> 
          let tl, env = map_typs env binders [t] in
          let binders' = match x with 
            | Inl x -> push_vbinder binders (Some x)
            | _ -> binders in
          let el, env = map_exps_with_binders env [(binders, e1); (binders', e2)] in 
          [], tl, el, env 
        | Exp_let((true, bvdt_tl), e) ->
          let tl = List.map (fun (_, t, _) -> t) bvdt_tl in
          let el = List.map (fun (_, _, e) -> e) bvdt_tl in
          let tl, env = map_typs env binders tl in
          let binders = List.fold_left (fun binders (x, _, _) -> match x with 
            | Inl x -> push_vbinder binders (Some x)
            | _ -> binders) binders bvdt_tl in 
          let el, env = map_exps env binders (el@[e]) in
          [], tl, el, env 
        | Exp_let _ -> failwith "impossible"
    in
    combine_exp e (kl, tl, el) env in
  map_exp env binders e
    
let combine_kind k (kl, tl, el) env = 
  let k' = match k.n, kl, tl with 
    | Kind_uvar _, [], []
    | Kind_type, [], [] 
    | Kind_effect, [], []
    | Kind_unknown, [], [] -> (fun p -> Util.return_all k)
    | Kind_abbrev(kabr, _), [k], _ -> 
      let rec reconstruct x = match x with
        | ([], [], []) -> []
        | (Inl _::args, t::tl, el) -> Inl t::reconstruct (args, tl, el)
        | (Inr _::args, tl, e::el) -> Inr e::reconstruct (args, tl, el)
        | _ -> failwith "impossible" in
      let args = reconstruct (snd kabr, tl, el) in 
      mk_Kind_abbrev((fst kabr, args), k)
    | Kind_tcon (aopt, k1, k2, imp), [k1';k2'], [] -> mk_Kind_tcon(aopt, k1', k2', imp)
    | Kind_dcon (xopt, t, k, imp), [k'], [t'] -> mk_Kind_dcon(xopt, t', k', imp)
    | _ -> failwith "impossible" in
  k' k.pos, env
    
let combine_typ t (kl, tl, cl, el) env =
  let t = compress_typ t in 
  let w f = f t.tk t.pos in
  let t' = match t.n, kl, tl, cl, el with 
    | Typ_unknown, [], [], [], []
    | Typ_btvar _, [], [], [], []  
    | Typ_const _, [], [], [], [] -> t
    | Typ_lam(x, t1, t2), [], [t1';t2'], [], [] ->     w <| mk_Typ_lam(x, t1', t2')
    | Typ_app(t1, t2, imp), [], [t1';t2'], [], [] ->   w <| mk_Typ_app(t1', t2', imp)
    | Typ_refine(x, t1, t2), [], [t1';t2'], [], [] ->  w <| mk_Typ_refine(x, t1', t2')
    | Typ_fun(x, t1, t2, imp), [], [t1'], [t2'], [] -> w <| mk_Typ_fun(x, t1', t2', imp)
    | Typ_tlam(a, k, t), [k'], [t'], [], [] ->         w <| mk_Typ_tlam(a, k', t')
    | Typ_univ(a, k, t), [k'], [], [t'], [] ->         w <| mk_Typ_univ(a, k', t')
    | Typ_dep(t, e, imp), [], [t'], [], [e'] ->        w <| mk_Typ_dep(t', e', imp)
    | Typ_uvar(x, k), [k'], [], [], [] ->              w <| mk_Typ_uvar'(x, k')
    | Typ_ascribed(_,_), [k'], [t'], [], [] ->         w <| mk_Typ_ascribed'(t', k')
    | Typ_meta(Meta_comp _), [], [], [c], [] ->        w <| mk_Typ_meta'(Meta_comp c)
    | Typ_meta(Meta_named(_, l)), [], [t'], [], [] ->  w <| mk_Typ_meta'(Meta_named(t', l))
    | Typ_meta(Meta_pattern _), [], _, _, _ ->         
      let pp = Meta_pattern(List.hd tl, (List.tl tl |> List.map Inl)@(el |> List.map Inr)) in
      w <| mk_Typ_meta'(pp)
    | Typ_meta(Meta_uvar_t_app(_, u)), [], [t], [], [] ->
      w <| mk_Typ_meta' (Meta_uvar_t_app(t, u))
    | _ -> failwith "impossible" in
  t', env

let combine_exp e (kl,tl,el) env = 
  let w f = f e.tk e.pos in
  let e' = match e.n, kl, tl, el with 
    | Exp_bvar _, [], [], []  
    | Exp_fvar _, [], [], [] 
    | Exp_constant _, [], [], [] -> e 
    | Exp_uvar(uv, _), [], [t], [] ->            w <| mk_Exp_uvar'(uv, t)
    | Exp_abs(x, t, e), [], [t'], [e'] ->        w <| mk_Exp_abs(x, t', e')
    | Exp_tabs(a, k, e), [k'], [], [e'] ->       w <| mk_Exp_tabs(a, k', e')
    | Exp_app(e1, e2, imp), [], [], [e1';e2'] -> w <| mk_Exp_app(e1', e2', imp)
    | Exp_tapp(e, t), [], [t'], [e'] ->          w <| mk_Exp_tapp(e', t')
    | Exp_match(e1, eqns), [], [], e1'::el -> 
      let rec mk_eqns eqns el = match eqns, el with 
        | (p,None, _)::eqns', e::el' -> (p, None, e)::mk_eqns eqns' el'
        | (p,Some _, _)::eqns', w::e::el' -> (p, Some w, e)::mk_eqns eqns' el'
        | [], [] -> []
        | _ -> failwith "impossible" in
                                                 w <| mk_Exp_match(e1', mk_eqns eqns el)
    | Exp_ascribed(e, t), [], [t'], [e'] ->      w <| mk_Exp_ascribed'(e', t')
    | Exp_let((x, lbs), e), [], _, _ ->
        (match Util.first_N (List.length lbs) el with 
           | el, [e'] -> 
              let lbs' = List.map3 (fun (lbname, _, _) t e -> (lbname, t, e)) lbs tl el in
              w <| mk_Exp_let((x, lbs'), e')
           | _ -> failwith "impossible")
    | Exp_meta(Meta_desugared(_, tag)), [], [], [e] -> w <| mk_Exp_meta' (Meta_desugared(e, tag))
    | Exp_meta(Meta_uvar_e_app(_, u)), [], [], [e] ->
      w <| mk_Exp_meta' (Meta_uvar_e_app(e, u))
    | _ -> failwith "impossible" in
  e', env

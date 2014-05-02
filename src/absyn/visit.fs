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

let rec compress_typ_aux pos typ = match typ.t with
  | Typ_uvar (uv,k) -> 
      begin
        match Unionfind.find uv with 
          | Fixed typ -> compress_typ_aux pos typ
          | _ -> typ
      end
  | Typ_ascribed(t, _)
  | Typ_meta(Meta_pos(t, _)) when pos -> compress_typ_aux pos t
  | _ -> typ
let compress_typ typ = compress_typ_aux true typ
let compress_typ_uvars typ = compress_typ_aux false typ

let rec compress_exp_aux meta exp = match exp with 
  | Exp_uvar (uv, _) -> 
    begin
      match Unionfind.find uv with 
        | Fixed e -> compress_exp_aux meta e 
        | _ -> exp
    end
  | Exp_ascribed(e, _)
  | Exp_meta(Meta_info(e, _, _))
  | Exp_meta(Meta_desugared(e, _)) when meta -> compress_exp_aux meta e
  | _ -> exp
let compress_exp e = compress_exp_aux true e
let compress_exp_uvars e = compress_exp_aux false e
  
let rec compress_kind kind = match kind with 
  | Kind_uvar uv -> 
    begin
      match Unionfind.find uv with 
        | Fixed k -> compress_kind k
        | _ -> kind
    end
  | _ -> kind

let left ext benv btv = match ext benv (Inl btv) with 
  | benv, Inl bvd -> benv, bvd
  | _ -> failwith "impossible" 
let right ext benv bvv = match ext benv (Inr bvv) with 
  | benv, Inr bvd -> benv, bvd
  | _ -> failwith "impossible" 
  
(* Utilities for recursively descending AST and visiting 
   the leaves of a term while gathering a context of names.
   Useful for implementing substitutions, computing freevars etc. *)
let rec visit_kind'
    (h: 'env -> 'benv -> kind -> ('env * kind))
    (f: 'env -> 'benv -> typ -> ('env * typ))
    (g: 'env -> 'benv -> exp -> ('env * exp))
    (l: 'env -> exp -> exp) 
    (ext: 'benv -> either<btvar, bvvar> -> ('benv * either<btvdef,bvvdef>))
    (env:'env) (benv:'benv) (k:kind) (cont: ('env * kind) -> 'res) : 'res =
  let k = compress_kind k in 
  match k with
    | Kind_uvar _ 
    | Kind_star
    | Kind_unknown -> cont (h env benv k)
    | Kind_tcon(aopt, k, k', imp) ->
        visit_kind' h f g l ext env benv k
          (fun (env, k) ->
             let benv, aopt = match aopt with
               | None -> benv, None
               | Some a ->
                   let benv, bvd = left ext benv (withsort a k) in
                     benv, Some bvd in (* Note: previously, with qkind, we were extending the benv before folding over k *)
               visit_kind' h f g l ext env benv k'
                 (fun (env, k') ->
                    cont (env, Kind_tcon(aopt, k, k', imp))))
    | Kind_dcon(xopt, t, k', imp) ->
        visit_typ' h f g l ext env benv t
          (fun (env, t) ->
             let benv, xopt = match xopt with
               | None -> benv, None
               | Some x -> let benv, bvd = right ext benv (withsort x t) in benv, Some bvd in
               visit_kind' h f g l ext env benv k'
                 (fun (env, k') ->
                    cont (env, Kind_dcon(xopt, t, k', imp))))
and visit_typ'
    (h: 'env -> 'benv -> kind -> ('env * kind))
    (f: 'env -> 'benv -> typ -> ('env * typ))
    (g: 'env -> 'benv -> exp -> ('env * exp))
    (l: 'env -> exp -> exp) (* transforms labels *)
    (ext: 'benv -> either<btvar, bvvar> -> ('benv * either<btvdef,bvvdef>))
    (env:'env) (benv:'benv) (t:typ) (cont:('env * typ) -> 'res) : 'res =
  let t_top = compress_typ t in
  let t = t_top in
  let wk = withkind t.k in
  match t.t with
    | Typ_uvar (_, k) ->
      let env, t' = f env benv t in
      (match t'.t with
        | Typ_uvar(uv, k) ->
          visit_kind' h f g l ext env benv k
            (fun (env, k) ->
              cont (env, withkind t.k <| Typ_uvar(uv, k)))
        | _ ->
          cont (env, t'))
    | Typ_btvar btv -> 
      (match !btv.v.instantiation with 
        | None -> 
          let env, t' = f env benv t in
          cont (env, t')
        | Some t -> 
          visit_typ' h f g l ext env benv t cont)
        
    | Typ_const _
    | Typ_unknown ->
      let env, t' = f env benv t in
      cont (env, t')
    | _ ->
      match t.t with
        | Typ_fun (nopt, t1, t2, imp) ->
          visit_typ' h f g l ext env benv t1
            (fun (env, t1') ->
              let benv', nopt' = match nopt with
                | None -> benv, nopt
                | Some bvd ->
                  let benv, bvd' = right ext benv (withsort bvd t1) in
                  benv, Some bvd' in
              visit_typ' h f g l ext env benv' t2
                (fun (env, t2') ->
                  cont (env, wk <| Typ_fun(nopt', t1', t2', imp))))
            
        | Typ_univ (bvd, k,  t) ->
          let benv', bvd' = left ext benv (withsort bvd k) in
          visit_typ' h f g l ext env benv' t
            (fun (env, t') ->
              visit_kind' h f g l ext env benv' k
                (fun (env, k') ->
                      cont (env, wk <| Typ_univ(bvd', k', t'))))
            
        | Typ_refine (bvd, t, form) ->
          visit_typ' h f g l ext env benv t
            (fun (env, t') ->
              let benv', bvd' = right ext benv (withsort bvd t) in
              visit_typ' h f g l ext env benv' form
                (fun (env, form') ->
                  cont (env, wk <| Typ_refine(bvd', t', form'))))

        | Typ_app(t1, t2, imp) ->
          visit_typ' h f g l ext env benv t1
            (fun (env, t1') ->
              visit_typ' h f g l ext env benv t2
                (fun (env, t2') ->
                  cont (env, wk <| Typ_app(t1', t2', imp))))

        | Typ_dep({t=Typ_const v; k=k'}, str, imp) 
            when lid_equals Const.lbl_lid v.v -> 
          cont (env, wk <| Typ_dep(withkind k' <| Typ_const(v), l env str, imp))
            
        | Typ_dep (t, e, imp) ->
          visit_typ' h f g l ext env benv t
            (fun (env, t') ->
              visit_exp' h f g l ext env benv e
                (fun (env, e') ->
                  cont (env, wk <| Typ_dep(t', e', imp))))

        | Typ_lam(x, t, t') ->
          visit_typ' h f g l ext env benv t
            (fun (env, t) ->
              let benv', bvd' = right ext benv (withsort x t) in
              visit_typ' h f g l ext env benv' t'
                (fun (env, t') ->
                  cont (env, wk <| Typ_lam(bvd', t, t'))))

        | Typ_tlam(bvd, k, t) ->
          let benv', bvd' = left ext benv (withsort bvd k) in
          visit_typ' h f g l ext env benv' t
            (fun (env, t') ->
              visit_kind' h f g l ext env benv' k
                (fun (env, k') ->
                  cont (env, wk <| Typ_tlam(bvd', k', t'))))
            
        | Typ_ascribed(t, k) ->
          visit_typ' h f g l ext env benv t
            (fun (env, t') ->
              visit_kind' h f g l ext env benv k
                (fun (env, k') ->
                  cont (env, wk <| Typ_ascribed(t,k))))

        | Typ_meta (Meta_cases tl) ->
          visit_typs' h f g l ext env benv tl
            (fun (env, tl') -> cont (env, wk <| Typ_meta(Meta_cases tl')))

        | Typ_meta (Meta_tid i) ->
          cont (env, wk <| Typ_meta(Meta_tid i))

        | Typ_meta (Meta_pattern(t, ps)) -> 
          let rec aux env ps cont = match ps with 
            | [] -> cont (env, [])
            | Inl t::tl ->  visit_typ' h f g l ext env benv t (fun (env, t') -> 
              aux env tl (fun (env, accum) -> cont (env, Inl t'::accum)))
            | Inr v::tl ->  visit_exp' h f g l ext env benv v (fun (env, e') -> 
              aux env tl (fun (env, accum) -> cont (env, Inr e'::accum))) in 
          visit_typ' h f g l ext env benv t 
            (fun (env, t') -> aux env ps (fun (env, ps) -> cont (env, wk <| Typ_meta(Meta_pattern(t', ps)))))

        | _ -> failwith "Unexpected type"

and visit_exp'
    (h: 'env -> 'benv -> kind -> ('env * kind))
    (f: 'env -> 'benv -> typ -> ('env * typ))
    (g: 'env -> 'benv -> exp -> ('env * exp))
    (l: 'env -> exp -> exp)
    (ext: 'benv -> either<btvar, bvvar> -> ('benv * either<btvdef,bvvdef>))
    (env:'env) (benv:'benv) (e:exp) (cont : ('env * exp) -> 'res) : 'res =
  let extl b l = match ext b l with
    | (x, Inl y) -> (x,y) 
    | _ -> failwith "Unexpected result" in
  let extr b l = match ext b l with
    | (x, Inr y) -> (x,y) 
    | _ -> failwith "Unexpected result" in
  let e = compress_exp_uvars e in 
    match e with
    | Exp_meta(Meta_datainst _) -> failwith "impossible"
    | Exp_meta(Meta_info(e, t, p)) -> 
      visit_exp' h f g l ext env benv e 
        (fun (env, e') -> 
//          visit_typ' h f g l ext env benv t
//            (fun (env, t) -> 
              cont (env, Exp_meta(Meta_info(e', t, p))))
//              )

    | Exp_meta(Meta_desugared(e, tag)) -> 
      visit_exp' h f g l ext env benv e 
        (fun (env, e') -> 
          cont (env, Exp_meta(Meta_desugared(e', tag))))
                    
    | Exp_bvar bv -> 
      (match !bv.v.instantiation with 
        | None -> cont (g env benv e)
        | Some e -> visit_exp' h f g l ext env benv e cont)
    | Exp_fvar _
    | Exp_constant _ 
    | Exp_uvar _ -> cont (g env benv e)
   
    | Exp_primop(op, el) ->
      visit_exps' h f g l ext env benv el
        (fun (env, el) ->
          cont (env, Exp_primop(op, el)))
        
    | Exp_abs (bvd, t, e) ->
      visit_typ' h f g l ext env benv t
        (fun (env, t') ->
          let benv', bvd' = extr benv (Inr (withsort bvd t)) in
          visit_exp' h f g l ext env benv' e
            (fun (env, e') ->
              cont (env, Exp_abs(bvd', t', e'))))
        
    | Exp_tabs(bvd, k, e) ->
      visit_kind' h f g l ext env benv k
        (fun (env, k') ->
          let benv', bvd' = extl benv (Inl (withsort bvd k)) in
          visit_exp' h f g l ext env benv' e
            (fun (env, e') ->
              cont (env, Exp_tabs(bvd', k', e'))))
        
    | Exp_app (e1, e2, imp) ->
      visit_exp' h f g l ext env benv e1
        (fun (env, e1') ->
          visit_exp' h f g l ext env benv e2
            (fun (env, e2') ->
              cont (env, Exp_app(e1', e2', imp))))
        
    | Exp_tapp (e, t) ->
      visit_exp' h f g l ext env benv e
        (fun (env, e') ->
          visit_typ' h f g l ext env benv t
            (fun (env, t') ->
              cont (env, Exp_tapp(e',t'))))
        
    | Exp_match(e, eqns) ->
      let rec visit_pat h f g l ext env benv pat cont = match pat with
        | Pat_var bv -> 
           let benv', bvd' = extr benv (Inr (withsort bv tun)) in
              cont (env, benv', Pat_var bvd')
        | Pat_tvar btv -> 
           let benv', bvd' = extl benv (Inl (withsort btv kun)) in
              cont (env, benv', Pat_tvar bvd')
        | Pat_cons(c, pats) -> 
          visit_pats h f g l ext env benv pats 
            (fun (env, benv, pats) ->  cont (env, benv, Pat_cons(c, pats))) 
        | Pat_constant c -> 
          cont (env, benv, pat)
        | Pat_disj [] -> failwith "impossible"
        | Pat_disj (p::ps) -> 
          visit_pat h f g l ext env benv p 
            (fun (env, benv, p) -> 
              visit_pats h f g l ext env benv ps
                (fun (_, _, ps) ->  cont (env, benv, Pat_disj(p::ps))))
        | Pat_wild
        | Pat_twild -> cont (env, benv, pat)
        | Pat_withinfo (p, r) -> 
          visit_pat h f g l ext env benv p 
            (fun (env, benv, p) -> 
              cont (env, benv, Pat_withinfo(p, r)))
          
      and visit_pats h f g l ext env benv pats cont = match pats with
        | [] -> cont (env, benv, pats)
        | hd::tl -> visit_pat h f g l ext env benv hd (fun (env, benv, hd) -> 
          visit_pats h f g l ext env benv tl (fun (env, benv, tl) -> 
            cont (env, benv, hd::tl))) in
      
      let rec visit_eqns env benv eqns cont = match eqns with
        | [] -> cont (env, [])
        | (pat, wopt, br)::rest -> 
          visit_pat h f g l ext env benv pat
            (fun (env, benv', pat') -> 
              match wopt with 
                | None -> 
                  visit_exp' h f g l ext env benv' br 
                    (fun (env, br') -> 
                      visit_eqns env benv rest 
                        (fun (env, rest') -> 
                          cont (env, (pat', None, br')::rest')))
                | Some w -> 
                  visit_exp' h f g l ext env benv' w 
                    (fun (env, w') -> 
                      visit_exp' h f g l ext env benv' br 
                        (fun (env, br') -> 
                          visit_eqns env benv rest 
                            (fun (env, rest') -> 
                              cont (env, (pat', Some w', br')::rest'))))) in
      visit_exp' h f g l ext env benv e
        (fun (env, e) ->
          visit_eqns env benv eqns
            (fun (env, eqns) ->
              cont (env, Exp_match(e, eqns))))
        
    | Exp_ascribed (e,t) -> 
      visit_exp' h f g l ext env benv e
        (fun (env, e') ->
          visit_typ' h f g l ext env benv t
            (fun (env, t') ->
              cont (env, Exp_ascribed(e',t'))))
        
    | Exp_let ((false,lbs), e) ->
      let rec binders_visit env benv lbs cont = match lbs with
        | [] -> cont (env, benv, [])
        | (lbname,t,e)::rest ->
          visit_exp' h f g l ext env benv e
            (fun (env, e') ->
              visit_typ' h f g l ext env benv t
                (fun (env, t') ->
                  let benv', lbname' = match lbname with
                    | Inl bv -> 
                      let benv', bv' = right ext benv (withsort bv t) in
                      benv', Inl bv'
                    | _ -> benv, lbname in
                  binders_visit env benv' rest (fun (env, benv, accum) ->
                    cont (env, benv, (lbname',t',e')::accum)))) in
      binders_visit env benv lbs
        (fun (env, benv', lbs') ->
          visit_exp' h f g l ext env benv' e
            (fun (env, e') -> cont (env, Exp_let((false, lbs'), e'))))
        
    | Exp_let ((true, lbs), e) ->
      let benv', lbs' = List.fold_left
        (fun (benv, out) (lbname,t,e) ->
          let benv', lbname' = match lbname with 
            | Inl bv -> 
              let benv', bv' = right ext benv (withsort bv t) in
              benv', Inl bv'
            | Inr _ -> benv, lbname in 
          benv', (lbname', t, e)::out) (benv,[]) lbs in
      let names, typs, exps = List.unzip3 lbs' in
      visit_typs' h f g l ext env benv' typs
        (fun (env, tl) ->
          visit_exps' h f g l ext env benv' exps
            (fun (env, el) ->
              let lbs' = List.zip3 names typs exps in
              visit_exp' h f g l ext env benv' e
                (fun (env, e') ->
                  cont (env, Exp_let((true, lbs'), e')))))

and visit_typs'
    (h: 'env -> 'benv -> kind -> ('env * kind))
    (f: 'env -> 'benv -> typ -> ('env * typ))
    (g: 'env -> 'benv -> exp -> ('env * exp))
    (l: 'env -> exp -> exp)
    (ext: 'benv -> either<btvar, bvvar> -> ('benv * either<btvdef,bvvdef>))
    (env:'env) (benv:'benv) (ts:list<typ>) (cont:('env * list<typ>) -> 'res) : 'res =
  let rec aux env tl cont = match tl with
    | [] -> cont (env, [])
    | t::tl -> visit_typ' h f g l ext env benv t (fun (env,t') -> aux env tl (fun (env, accum) -> cont (env, t'::accum)))
  in
    aux env ts cont 

and visit_exps'
    (h: 'env -> 'benv -> kind -> ('env * kind))
    (f: 'env -> 'benv -> typ -> ('env * typ))
    (g: 'env -> 'benv -> exp -> ('env * exp))
    (l: 'env -> exp -> exp)
    (ext: 'benv -> either<btvar, bvvar> -> ('benv * either<btvdef,bvvdef>))
    (env:'env) (benv:'benv) (es:list<exp>) (cont:('env * list<exp>) -> 'res) : 'res =
  
  let rec aux env tl cont = match tl with
    | [] -> cont (env, [])
    | e::tl -> visit_exp' h f g l ext env benv e (fun (env,t') -> aux env tl (fun (env, accum) -> cont (env, t'::accum)))
  in
    aux env es cont

and visit_either_l'
    (h: 'env -> 'benv -> kind -> ('env * kind))
    (f: 'env -> 'benv -> typ -> ('env * typ))
    (g: 'env -> 'benv -> exp -> ('env * exp))
    (l: 'env -> exp -> exp)
    (ext: 'benv -> either<btvar, bvvar> -> ('benv * either<btvdef,bvvdef>))
    (env:'env) (benv:'benv) (es:list<either<typ,exp>>) (cont:('env * list<either<typ,exp>>) -> 'res) : 'res =
  let rec aux env tl cont = match tl with
    | [] -> cont (env, [])
    | (Inr e)::tl -> visit_exp' h f g l ext env benv e (fun (env,e') -> aux env tl (fun (env, accum) -> cont (env, Inr e'::accum)))
    | (Inl t)::tl -> visit_typ' h f g l ext env benv t (fun (env,t') -> aux env tl (fun (env, accum) -> cont (env, Inl t'::accum)))
  in
    aux env es cont
      
let visit_typs h f g l ext env benv t = visit_typs' h f g l ext env benv t (fun x -> x)
let visit_typ h f g l ext env benv t = visit_typ' h f g l ext env benv t (fun x -> x)
let visit_exp h f g l ext env benv t = visit_exp' h f g l ext env benv t (fun x -> x)
let visit_kind h f g l ext env benv t = visit_kind' h f g l ext env benv t (fun x -> x)

let visit_simple skel
    (h: 'env -> kind -> ('env * kind))
    (f: 'env -> typ -> ('env * typ))
    (g: 'env -> exp -> ('env * exp))
    (env:'env) (t:'kte) : ('env * 'kte) =
  let null_extension benv (x:either<btvar, bvvar>) = match x with
    | Inl tv -> (benv, Inl tv.v)
    | Inr xv -> (benv, Inr xv.v) in
  skel
    (fun env _ k -> h env k)
    (fun env _ t -> f env t)
    (fun env _ e -> g env e)
    (fun _ e -> e)
    null_extension
    env () t

let visit_kind_simple f = visit_simple visit_kind f
let visit_typ_simple f = visit_simple visit_typ f 
let visit_exp_simple f = visit_simple visit_exp f

(**********************************************************************************)
(* A more general way to reduce types. Would be good to migrate to this uniformly *)
(**********************************************************************************)
type binders = list<either<btvdef, bvvdef>>
type mapper<'env, 'm, 'n> =
    ('env -> binders -> kind -> (kind * 'env))
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
    (map_kind': mapper<'env, kind, kind>)
    (map_typ': mapper<'env, typ, typ>)
    (map_exp': mapper<'env, exp, exp>)
    (combine_kind: (kind -> (list<kind> * list<typ> * list<exp>) -> 'env -> (kind * 'env)))
    (combine_typ: (typ -> (list<kind> * list<typ> * list<exp>) -> 'env -> (typ * 'env)))
    (combine_exp: (exp -> (list<kind> * list<typ> * list<exp>) -> 'env -> (exp * 'env))) (env:'env) binders k: (kind * 'env) =
  let rec visit_kind env binders k =
    let k = compress_kind k in
    let kl, tl, el, env =   
      match k with 
        | Kind_uvar _
        | Kind_star 
        | Kind_unknown -> [], [], [], env
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
    (map_kind': mapper<'env, kind, kind>)
    (map_typ': mapper<'env, typ, typ>)
    (map_exp': mapper<'env, exp, exp>)
    (combine_kind: (kind -> (list<kind> * list<typ> * list<exp>) -> 'env -> (kind * 'env)))
    (combine_typ: (typ -> (list<kind> * list<typ> * list<exp>) -> 'env -> (typ * 'env)))
    (combine_exp: (exp -> (list<kind> * list<typ> * list<exp>) -> 'env -> (exp * 'env))) (env:'env) binders t : (typ * 'env) =
  let rec map_typs env binders tl = 
    let tl, _, env = List.fold_left (fun (out, binders, env) (xopt, t) -> 
      let t, env = map_typ env binders t in
      let binders = push_vbinder binders xopt in 
      t::out, binders, env) ([], binders, env) tl in
    List.rev tl, env 
  and visit_typ env binders t = 
    let kl, tl, el, env = match (compress_typ t).t with 
      | Typ_unknown
      | Typ_btvar _   
      | Typ_const _ -> [],[],[], env
      | Typ_app(t1, t2, imp) -> 
        let tl, env = map_typs env binders [(None, t1); (None, t2)] in 
        [], tl, [], env 
      | Typ_lam(x, t1, t2)
      | Typ_refine(x, t1, t2) -> 
        let tl, env = map_typs env binders [(Some x, t1); (None, t2)] in 
        [], tl, [], env 
      | Typ_fun(xopt, t1, t2, imp) -> 
        let tl, env = map_typs env binders [(xopt,t1);(None, t2)] in
        [], tl, [], env 
      | Typ_univ(a, k, t) 
      | Typ_tlam(a, k, t) ->
        let k, env = map_kind env binders k in
        let t, env = map_typ env (push_tbinder binders (Some a)) t in
        [k], [t], [], env
      | Typ_dep(t, e, imp) -> 
        let t, env = map_typ env binders t in
        let e, env = map_exp env binders e in
        [], [t], [e], env
      | Typ_ascribed(t,k) ->  
        let t, env = map_typ env binders t in
        let k, env = map_kind env binders k in
        [k], [t], [], env
      | Typ_uvar(_, k) -> 
        let k, env = map_kind env binders k in
        [k], [], [], env
      | Typ_meta(Meta_pos(t, _)) ->
        let t, env = map_typ env binders t in
        [], [t], [], env 
      | Typ_meta(Meta_tid _) -> 
        [], [], [], env
      | Typ_meta(Meta_cases tl) -> 
        let tl, env = map_typs env binders (List.map (fun t -> (None, t)) tl) in 
        [], tl, [], env
      | Typ_meta(Meta_pattern(t,ps)) -> 
        let t,env = map_typ env binders t in 
        let tpats, vpats, env = List.fold_left (fun (tpats, vpats, env) -> function
          | Inl t -> let t, env = map_typ env binders t in (t::tpats, vpats, env)
          | Inr e -> let e, env = map_exp env binders e in (tpats, e::vpats, env)) ([], [], env) ps in 
        [], t::tpats, vpats, env in
    combine_typ t (kl, tl, el) env 
  and map_kind env binders k = reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k 
  and map_typ env binders t = map_typ' map_kind visit_typ map_exp env binders t
  and map_exp env binders e = reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e  
  in
  map_typ env binders t
    
and reduce_exp 
    (map_kind': mapper<'env, kind, kind>)
    (map_typ': mapper<'env, typ, typ>)
    (map_exp': mapper<'env, exp, exp>)
    (combine_kind: (kind -> (list<kind> * list<typ> * list<exp>) -> 'env -> (kind * 'env)))
    (combine_typ: (typ -> (list<kind> * list<typ> * list<exp>) -> 'env -> (typ * 'env)))
    (combine_exp: (exp -> (list<kind> * list<typ> * list<exp>) -> 'env -> (exp * 'env))) (env:'env) binders e : (exp * 'env) =
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
     let kl, tl, el, env = match e with 
        | Exp_meta(Meta_datainst _) -> failwith "impossible"
        | Exp_meta(Meta_info(e, t, _)) -> 
          let e, env = map_exp env binders e in 
          let t, env = map_typ env binders t in 
          [], [t], [e], env
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
        | Exp_primop(_, el) ->
          let el, env = map_exps env binders el in
          [], [], el, env in
    combine_exp e (kl, tl, el) env in
  map_exp env binders e
    
let combine_kind k (kl, tl, el) env = 
  let k' = match k, kl, tl with 
    | Kind_uvar _, [], []
    | Kind_star, [], [] 
    | Kind_unknown, [], [] -> k
    | Kind_tcon (aopt, k1, k2, imp), [k1';k2'], [] -> Kind_tcon(aopt, k1', k2', imp)
    | Kind_dcon (xopt, t, k, imp), [k'], [t'] -> Kind_dcon(xopt, t', k', imp) 
    | _ -> failwith "impossible" in
  k', env
    
let combine_typ t (kl, tl, el) env =
  let t = compress_typ t in 
  let t' = match t.t, kl, tl, el with 
    | Typ_unknown, [], [], []
    | Typ_btvar _, [], [], []  
    | Typ_const _, [], [], [] -> t.t
    | Typ_lam(x, t1, t2), [], [t1';t2'], [] -> Typ_lam(x, t1', t2')
    | Typ_app(t1, t2, imp), [], [t1';t2'], [] -> Typ_app(t1',t2', imp)
    | Typ_refine(x, t1, t2), [], [t1';t2'], [] -> Typ_refine(x, t1', t2')
    | Typ_fun(x, t1, t2, imp), [], [t1';t2'], [] -> Typ_fun(x, t1', t2', imp)
    | Typ_tlam(a, k, t), [k'], [t'], [] -> Typ_tlam(a, k', t')
    | Typ_univ(a, k, t), [k'], [t'], [] -> Typ_univ(a, k', t')
    | Typ_dep(t, e, imp), [], [t'], [e'] -> Typ_dep(t', e', imp)
    | Typ_uvar(x, k), [k'], [], [] -> Typ_uvar(x, k')
    | Typ_ascribed(_,_), [k'], [t'], [] -> Typ_ascribed(t', k')
    | Typ_meta(Meta_pos(_, r)), [], [t'], [] -> Typ_meta(Meta_pos(t', r))
    | Typ_meta(Meta_tid _), [], [], [] -> t.t
    | Typ_meta(Meta_cases _), [], _, [] -> Typ_meta(Meta_cases tl) 
    | Typ_meta(Meta_pattern _), [], _, _ -> Typ_meta(Meta_pattern(List.hd tl, (List.tl tl |> List.map Inl)@(el |> List.map Inr)))
    | _ -> failwith "impossible" in
  withkind t.k t', env

let combine_exp e (kl,tl,el) env = 
  let e' = match e.v, kl, tl, el with 
    | Exp_bvar _, [], [], []  
    | Exp_fvar _, [], [], [] 
    | Exp_constant _, [], [], [] -> e.v
    | Exp_uvar(uv, _), [], [t], [] -> Exp_uvar(uv, t)
    | Exp_abs(x, t, e), [], [t'], [e'] -> Exp_abs(x, t', e')
    | Exp_tabs(a, k, e), [k'], [], [e'] -> Exp_tabs(a, k', e')
    | Exp_app(e1, e2, imp), [], [], [e1';e2'] -> Exp_app(e1', e2', imp)  
    | Exp_tapp(e, t), [], [t'], [e'] -> Exp_tapp(e', t')
    | Exp_match(e1, eqns), [], [], e1'::el -> 
      let rec mk_eqns eqns el = match eqns, el with 
        | (p,None, _)::eqns', e::el' -> (p, None, e)::mk_eqns eqns' el'
        | (p,Some _, _)::eqns', w::e::el' -> (p, Some w, e)::mk_eqns eqns' el'
        | _ -> failwith "impossible" in
      Exp_match(e1', mk_eqns eqns el)
    | Exp_ascribed(e, t), [], [t'], [e'] -> Exp_ascribed(e', t')
    | Exp_let((x, lbs), e), [], _, _ ->
        (match Util.first_N (List.length lbs) el with 
           | el, [e'] -> 
              let lbs' = List.map3 (fun (lbname, _, _) t e -> (lbname, t, e)) lbs tl el in
              Exp_let((x, lbs'), e') 
           | _ -> failwith "impossible")
    | Exp_primop(x, es), [], [], _ -> Exp_primop(x, el)
    | Exp_meta(Meta_info(_, _, p)), [], [t], [e] -> 
      Exp_meta(Meta_info(e, t, p))
    | Exp_meta(Meta_desugared(_, tag)), [], [], [e] -> 
      Exp_meta(Meta_desugared(e, tag))
    | _ -> failwith "impossible" in
  withinfo e' e.sort e.p, env

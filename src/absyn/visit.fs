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

let rec compress typ = match typ with
  | Typ_uvar (uv,k) -> 
      begin
        match Unionfind.find uv with 
          | Fixed typ -> compress typ
          | _ -> typ
      end
  | Typ_meta(Meta_pos(t, _)) -> compress t
  | _ -> typ


(* Utilities for recursively descending AST and applying substitutions *)
let rec visit_kind'
    (f: 'env -> 'benv -> typ -> ('env * typ))
    (g: 'env -> 'benv -> exp' -> ('env * exp'))
    (l: 'env -> exp -> exp) 
    (ext: 'benv -> either<btvar, bvvar> -> ('benv * either<btvdef,bvvdef>))
    (env:'env) (benv:'benv) (k:kind) (cont: ('env * kind) -> 'res) : 'res =
  match k with
    | Kind_prop
    | Kind_erasable
    | Kind_star
    | Kind_unknown -> cont (env, k)
    | Kind_tcon(aopt, k, k') ->
        visit_kind' f g l ext env benv k
          (fun (env, k) ->
             let benv, aopt = match aopt with
               | None -> benv, None
               | Some a ->
                   let benv, Inl bvd = ext benv (Inl(withsort a k)) in
                     benv, Some bvd in (* Note: previously, with qkind, we were extending the benv before folding over k *)
               visit_kind' f g l ext env benv k'
                 (fun (env, k') ->
                    cont (env, Kind_tcon(aopt, k, k'))))
    | Kind_dcon(xopt, t, k') ->
        visit_typ' f g l ext env benv t
          (fun (env, t) ->
             let benv, xopt = match xopt with
               | None -> benv, None
               | Some x -> let benv, Inr bvd = ext benv (Inr(withsort x t)) in benv, Some bvd in
               visit_kind' f g l ext env benv k'
                 (fun (env, k') ->
                    cont (env, Kind_dcon(xopt, t, k'))))
and visit_typ'
    (f: 'env -> 'benv -> typ -> ('env * typ))
    (g: 'env -> 'benv -> exp' -> ('env * exp'))
    (l: 'env -> exp -> exp) (* transforms labels *)
    (ext: 'benv -> either<btvar, bvvar> -> ('benv * either<btvdef,bvvdef>))
    (env:'env) (benv:'benv) (t:typ) (cont:('env * typ) -> 'res) : 'res =
  let t_top = compress t in
  let t = t_top in
  match t with
    | Typ_uvar (_,k) ->
      let env, t' = f env benv t in
      (match t' with
        | Typ_uvar(uv, k) ->
          visit_kind' f g l ext env benv k
            (fun (env, k) ->
              cont (env, Typ_uvar(uv, k)))
        | _ ->
          cont (env, t'))
    | Typ_btvar btv -> 
      (match !btv.v.instantiation with 
        | None -> 
          let env, t' = f env benv t in
          cont (env, t')
        | Some t -> 
          visit_typ' f g l ext env benv t cont)
        
    | Typ_const _
    | Typ_unknown ->
      let env, t' = f env benv t in
      cont (env, t')
    | _ ->
      match t with
        | Typ_fun (nopt, t1, t2) ->
          visit_typ' f g l ext env benv t1
            (fun (env, t1') ->
              let benv', nopt' = match nopt with
                | None -> benv, nopt
                | Some bvd ->
                  let benv, (Inr bvd') = ext benv (Inr (withsort bvd t1)) in
                  benv, Some bvd' in
              visit_typ' f g l ext env benv' t2
                (fun (env, t2') ->
                  cont (env, Typ_fun(nopt', t1', t2'))))
            
        | Typ_univ (bvd, k,  t) ->
          let benv', (Inl bvd') = ext benv (Inl (withsort bvd k)) in
          visit_typ' f g l ext env benv' t
            (fun (env, t') ->
              visit_kind' f g l ext env benv' k
                (fun (env, k') ->
                      cont (env, Typ_univ(bvd', k', t'))))
            
        | Typ_refine (bvd, t, form) ->
          visit_typ' f g l ext env benv t
            (fun (env, t') ->
              let benv', (Inr bvd') = ext benv (Inr (withsort bvd t)) in
              visit_typ' f g l ext env benv' form
                (fun (env, form') ->
                  cont (env, Typ_refine(bvd', t', form'))))

        | Typ_app(t1, t2) ->
          visit_typ' f g l ext env benv t1
            (fun (env, t1') ->
              visit_typ' f g l ext env benv t2
                (fun (env, t2') ->
                  cont (env, Typ_app(t1', t2'))))

        | Typ_dep(Typ_const v, str) 
            when lid_equals Const.lbl_lid v.v -> 
          cont (env, Typ_dep(Typ_const(v), l env str))
            
        | Typ_dep (t, e) ->
          visit_typ' f g l ext env benv t
            (fun (env, t') ->
              visit_exp' f g l ext env benv e
                (fun (env, e') ->
                  cont (env, Typ_dep(t', e'))))

        | Typ_lam(x, t, t') ->
          visit_typ' f g l ext env benv t
            (fun (env, t) ->
              let benv', (Inr bvd') = ext benv (Inr (withsort x t)) in
              visit_typ' f g l ext env benv' t'
                (fun (env, t') ->
                  cont (env, Typ_lam(bvd', t, t'))))

        | Typ_tlam(bvd, k, t) ->
          let benv', (Inl bvd') = ext benv (Inl (withsort bvd k)) in
          visit_typ' f g l ext env benv' t
            (fun (env, t') ->
              visit_kind' f g l ext env benv' k
                (fun (env, k') ->
                  cont (env, Typ_tlam(bvd', k', t'))))
            
        | Typ_ascribed(t, k) ->
          visit_typ' f g l ext env benv t
            (fun (env, t') ->
              visit_kind' f g l ext env benv k
                (fun (env, k') ->
                  cont (env, Typ_ascribed(t,k))))

        | Typ_meta (Meta_cases tl) ->
          visit_typs' f g l ext env benv tl
            (fun (env, tl') -> cont (env, Typ_meta(Meta_cases tl')))

        | Typ_meta (Meta_tid i) ->
          cont (env, Typ_meta(Meta_tid i))

        | Typ_meta (Meta_pattern(t, ps)) -> 
          let rec aux env ps cont = match ps with 
            | [] -> cont (env, [])
            | Inl t::tl ->  visit_typ' f g l ext env benv t (fun (env, t') -> 
              aux env tl (fun (env, accum) -> cont (env, Inl t'::accum)))
            | Inr v::tl ->  visit_exp' f g l ext env benv v (fun (env, e') -> 
              aux env tl (fun (env, accum) -> cont (env, Inr e'::accum))) in 
          visit_typ' f g l ext env benv t 
            (fun (env, t') -> aux env ps (fun (env, ps) -> cont (env, Typ_meta(Meta_pattern(t', ps)))))

        | _ -> failwith "Unexpected type"


and visit_exp'
    (f: 'env -> 'benv -> typ -> ('env * typ))
    (g: 'env -> 'benv -> exp' -> ('env * exp'))
    (l: 'env -> exp -> exp)
    (ext: 'benv -> either<btvar, bvvar> -> ('benv * either<btvdef,bvvdef>))
    (env:'env) (benv:'benv) (e:exp) (contorig : ('env * exp) -> 'res) : 'res =
  let cont (env, exp') =
    visit_typ' f g l ext env benv e.sort
      (fun (env, sort') -> contorig (env, withinfo exp' sort' e.p)) in
  let extl b l = match ext b l with
    | (x, Inl y) -> (x,y) 
    | _ -> failwith "Unexpected result" in
  let extr b l = match ext b l with
    | (x, Inr y) -> (x,y) 
    | _ -> failwith "Unexpected result" in
    match e.v with
    | Exp_bvar bv -> 
      (match !bv.v.instantiation with 
        | None -> cont (g env benv e.v)
        | Some e -> visit_exp' f g l ext env benv e contorig)
    | Exp_fvar _
    | Exp_constant _ -> cont (g env benv e.v)
    | Exp_constr_app (v, args) -> 
      let env, _ = g env benv (Exp_fvar v) in
      visit_either_l' f g l ext env benv args 
        (fun (env, args) -> 
          cont (env, Exp_constr_app(v, args)))

    | Exp_primop(op, el) ->
      visit_exps' f g l ext env benv el
        (fun (env, el) ->
          cont (env, Exp_primop(op, el)))
        
    | Exp_abs (bvd, t, e) ->
      visit_typ' f g l ext env benv t
        (fun (env, t') ->
          let benv', bvd' = extr benv (Inr (withsort bvd t)) in
          visit_exp' f g l ext env benv' e
            (fun (env, e') ->
              cont (env, Exp_abs(bvd', t', e'))))
        
    | Exp_tabs(bvd, k, e) ->
      visit_kind' f g l ext env benv k
        (fun (env, k') ->
          let benv', bvd' = extl benv (Inl (withsort bvd k)) in
          visit_exp' f g l ext env benv' e
            (fun (env, e') ->
              cont (env, Exp_tabs(bvd', k', e'))))
        
    | Exp_app (e1, e2) ->
      visit_exp' f g l ext env benv e1
        (fun (env, e1') ->
          visit_exp' f g l ext env benv e2
            (fun (env, e2') ->
              cont (env, Exp_app(e1', e2'))))
        
    | Exp_tapp (e, t) ->
      visit_exp' f g l ext env benv e
        (fun (env, e') ->
          visit_typ' f g l ext env benv t
            (fun (env, t') ->
              cont (env, Exp_tapp(e',t'))))
        
    | Exp_match(e, eqns) ->
      let rec visit_pat f g l ext env benv pat cont = match pat with
        | Pat_var bv -> 
           let benv', bvd' = extr benv (Inr (withsort bv Typ_unknown)) in
              cont (env, benv', Pat_var bvd')
        | Pat_tvar btv -> 
           let benv', bvd' = extl benv (Inl (withsort btv Kind_unknown)) in
              cont (env, benv', Pat_tvar bvd')
        | Pat_cons(c, pats) -> 
          visit_pats f g l ext env benv pats 
            (fun (env, benv, pats) ->  cont (env, benv, Pat_cons(c, pats))) 
        | Pat_constant c -> 
          cont (env, benv, pat)
        | Pat_disj (p::ps) -> 
          visit_pat f g l ext env benv p 
            (fun (env, benv, p) -> 
              visit_pats f g l ext env benv ps
                (fun (_, _, ps) ->  cont (env, benv, Pat_disj(p::ps))))
        | Pat_wild
        | Pat_twild -> cont (env, benv, pat)
          
      and visit_pats f g l ext env benv pats cont = match pats with
        | [] -> cont (env, benv, pats)
        | hd::tl -> visit_pat f g l ext env benv hd (fun (env, benv, hd) -> 
          visit_pats f g l ext env benv tl (fun (env, benv, tl) -> 
            cont (env, benv, hd::tl))) in
      
      let rec visit_eqns env benv eqns cont = match eqns with
        | [] -> cont (env, [])
        | (pat, wopt, br)::rest -> 
          visit_pat f g l ext env benv pat
            (fun (env, benv', pat') -> 
              match wopt with 
                | None -> 
                  visit_exp' f g l ext env benv' br 
                    (fun (env, br') -> 
                      visit_eqns env benv rest 
                        (fun (env, rest') -> 
                          cont (env, (pat', None, br')::rest')))
                | Some w -> 
                  visit_exp' f g l ext env benv' w 
                    (fun (env, w') -> 
                      visit_exp' f g l ext env benv' br 
                        (fun (env, br') -> 
                          visit_eqns env benv rest 
                            (fun (env, rest') -> 
                              cont (env, (pat', Some w', br')::rest'))))) in
      visit_exp' f g l ext env benv e
        (fun (env, e) ->
          visit_eqns env benv eqns
            (fun (env, eqns) ->
              cont (env, Exp_match(e, eqns))))
        
    | Exp_ascribed (e,t) -> 
      visit_exp' f g l ext env benv e
        (fun (env, e') ->
          visit_typ' f g l ext env benv t
            (fun (env, t') ->
              cont (env, Exp_ascribed(e',t'))))
        
    | Exp_let (false, bvd_t_e_l, e) ->
      let rec binders_visit env benv bvd_t_e_l cont = match bvd_t_e_l with
        | [] -> cont (env, benv, [])
        | (bv,t,e)::rest ->
          visit_exp' f g l ext env benv e
            (fun (env, e') ->
              visit_typ' f g l ext env benv t
                (fun (env, t') ->
                  let benv', (Inr bv') = ext benv (Inr (withsort bv t)) in
                  binders_visit env benv' rest (fun (env, benv, accum) ->
                    cont (env, benv, (bv',t',e')::accum)))) in
      binders_visit env benv bvd_t_e_l
        (fun (env, benv', bvd_t_e_l) ->
          visit_exp' f g l ext env benv' e
            (fun (env, e') -> cont (env, Exp_let(false, bvd_t_e_l, e'))))
        
    | Exp_let (true, bvd_t_e_l, e) ->
      let benv', bvd_t_e_l' = List.fold_left
        (fun (benv, out) (bv,t,e) ->
          let benv', (Inr bv') = ext benv (Inr (withsort bv t)) in
          benv', (bv', t, e)::out) (benv,[]) bvd_t_e_l in
      let bvs, typs, exps = List.unzip3 bvd_t_e_l' in
      visit_typs' f g l ext env benv' typs
        (fun (env, tl) ->
          visit_exps' f g l ext env benv' exps
            (fun (env, el) ->
              let bvd_t_e_l' = List.zip3 bvs typs exps in
              visit_exp' f g l ext env benv' e
                (fun (env, e') ->
                  cont (env, Exp_let(true, bvd_t_e_l', e')))))
        
    | e -> failwith "Unexpected expression"


and visit_typs'
    (f: 'env -> 'benv -> typ -> ('env * typ))
    (g: 'env -> 'benv -> exp' -> ('env * exp'))
    (l: 'env -> exp -> exp)
    (ext: 'benv -> either<btvar, bvvar> -> ('benv * either<btvdef,bvvdef>))
    (env:'env) (benv:'benv) (ts:list<typ>) (cont:('env * list<typ>) -> 'res) : 'res =
  let rec aux env tl cont = match tl with
    | [] -> cont (env, [])
    | t::tl -> visit_typ' f g l ext env benv t (fun (env,t') -> aux env tl (fun (env, accum) -> cont (env, t'::accum)))
  in
    aux env ts cont 

and visit_exps'
    (f: 'env -> 'benv -> typ -> ('env * typ))
    (g: 'env -> 'benv -> exp' -> ('env * exp'))
    (l: 'env -> exp -> exp)
    (ext: 'benv -> either<btvar, bvvar> -> ('benv * either<btvdef,bvvdef>))
    (env:'env) (benv:'benv) (es:list<exp>) (cont:('env * list<exp>) -> 'res) : 'res =
  
  let rec aux env tl cont = match tl with
    | [] -> cont (env, [])
    | e::tl -> visit_exp' f g l ext env benv e (fun (env,t') -> aux env tl (fun (env, accum) -> cont (env, t'::accum)))
  in
    aux env es cont

and visit_either_l'
    (f: 'env -> 'benv -> typ -> ('env * typ))
    (g: 'env -> 'benv -> exp' -> ('env * exp'))
    (l: 'env -> exp -> exp)
    (ext: 'benv -> either<btvar, bvvar> -> ('benv * either<btvdef,bvvdef>))
    (env:'env) (benv:'benv) (es:list<either<typ,exp>>) (cont:('env * list<either<typ,exp>>) -> 'res) : 'res =
  let rec aux env tl cont = match tl with
    | [] -> cont (env, [])
    | (Inr e)::tl -> visit_exp' f g l ext env benv e (fun (env,e') -> aux env tl (fun (env, accum) -> cont (env, Inr e'::accum)))
    | (Inl t)::tl -> visit_typ' f g l ext env benv t (fun (env,t') -> aux env tl (fun (env, accum) -> cont (env, Inl t'::accum)))
  in
    aux env es cont
      
let visit_typs f g l ext env benv t = visit_typs' f g l ext env benv t (fun x -> x)
let visit_typ f g l ext env benv t = visit_typ' f g l ext env benv t (fun x -> x)
let visit_exp f g l ext env benv t = visit_exp' f g l ext env benv t (fun x -> x)
let visit_kind f g l ext env benv t = visit_kind' f g l ext env benv t (fun x -> x)

let visit_simple skel
    (f: 'env -> typ -> ('env * typ))
    (g: 'env -> exp' -> ('env * exp'))
    (env:'env) (t:'kte) : ('env * 'kte) =
  let null_extension benv (x:either<btvar, bvvar>) = match x with
    | Inl tv -> (benv, Inl tv.v)
    | Inr xv -> (benv, Inr xv.v) in
  skel
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
type mapper<'env, 'k, 't, 'e, 'm, 'n> =
    ('env -> binders -> kind -> ('k * 'env))
    -> ('env -> binders -> typ -> ('t * 'env))
    -> ('env -> binders -> exp -> ('e * 'env))
    -> 'env -> binders -> 'm -> ('n * 'env)

let push_tbinder binders = function 
  | None -> binders
  | Some a -> (Inl a)::binders
let push_vbinder binders = function 
  | None -> binders
  | Some a -> (Inr a)::binders

let rec reduce_kind 
    (map_kind': mapper<'env, 'k, 't, 'e, kind, 'k>)
    (map_typ': mapper<'env, 'k, 't, 'e, typ, 't>)
    (map_exp': mapper<'env, 'k, 't, 'e, exp, 'e>)
    (combine_kind: (kind -> ('k list * 't list * 'e list) -> 'env -> ('k * 'env)))
    (combine_typ: (typ -> ('k list * 't list * 'e list) -> 'env -> ('t * 'env)))
    (combine_exp: (exp -> ('k list * 't list * 'e list) -> 'env -> ('e * 'env))) (env:'env) binders kind : ('k * 'env) =
  let rec visit_kind env binders k =
    let kl, tl, el, env =   
      (match k(* .u *) with 
        | Kind_star 
        | Kind_prop
        | Kind_erasable
        | Kind_unknown -> [], [], [], env
        | Kind_tcon (aopt, k1, k2) -> 
          let k1, env = map_kind env binders k1 in
          let k2, env = map_kind env (push_tbinder binders aopt) k2 in
          [k1;k2], [], [], env
        | Kind_dcon (xopt, t, k) -> 
          let t, env = map_typ env binders t in
          let k, env = map_kind env (push_vbinder binders xopt) k in
          [k],[t],[],env) in
    combine_kind k (kl, tl, el) env 
  and map_kind env binders k = map_kind' visit_kind map_typ map_exp env binders k
  and map_typ env binders t = reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t 
  and map_exp env binders e = reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e
  in
  map_kind env binders kind
    
and reduce_typ 
    (map_kind': mapper<'env, 'k, 't, 'e, kind, 'k>)
    (map_typ': mapper<'env, 'k, 't, 'e, typ, 't>)
    (map_exp': mapper<'env, 'k, 't, 'e, exp, 'e>)
    (combine_kind: (kind -> ('k list * 't list * 'e list) -> 'env -> ('k * 'env)))
    (combine_typ: (typ -> ('k list * 't list * 'e list) -> 'env -> ('t * 'env)))
    (combine_exp: (exp -> ('k list * 't list * 'e list) -> 'env -> ('e * 'env))) (env:'env) binders typ : ('t * 'env) =
  let rec map_typs env binders tl = 
    let tl, _, env = List.fold_left (fun (out, binders, env) (xopt, t) -> 
      let t, env = map_typ env binders t in
      let binders = push_vbinder binders xopt in 
      t::out, binders, env) ([], binders, env) tl in
    List.rev tl, env 
  and visit_typ env binders t = 
    let kl, tl, el, env =   
      (match compress t with 
        | Typ_unknown
        | Typ_btvar _   
        | Typ_const _ -> [],[],[], env
        | Typ_app(t1, t2) -> 
          let tl, env = map_typs env binders [(None, t1); (None, t2)] in 
          [], tl, [], env 
        | Typ_lam(x, t1, t2)
        | Typ_refine(x, t1, t2) -> 
          let tl, env = map_typs env binders [(Some x, t1); (None, t2)] in 
          [], tl, [], env 
        | Typ_fun(xopt, t1, t2) -> 
          let tl, env = map_typs env binders [(xopt,t1);(None, t2)] in
          [], tl, [], env 
        | Typ_univ(a, k, t) 
        | Typ_tlam(a, k, t) ->
          let k, env = map_kind env binders k in
          let t, env = map_typ env (push_tbinder binders (Some a)) t in
          [k], [t], [], env
        | Typ_dep(t, e) -> 
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
        | Typ_meta(Meta_pos(t,_)) ->
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
          [], t::tpats, vpats, env)
    in 
    combine_typ t (kl, tl, el) env 
  and map_kind env binders k = reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k 
  and map_typ env binders t = map_typ' map_kind visit_typ map_exp env binders t
  and map_exp env binders e = reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e  
  in
  map_typ env binders typ
    
and reduce_exp 
    (map_kind': mapper<'env, 'k, 't, 'e, kind, 'k>)
    (map_typ': mapper<'env, 'k, 't, 'e, typ, 't>)
    (map_exp': mapper<'env, 'k, 't, 'e, exp, 'e>)
    (combine_kind: (kind -> ('k list * 't list * 'e list) -> 'env -> ('k * 'env)))
    (combine_typ: (typ -> ('k list * 't list * 'e list) -> 'env -> ('t * 'env)))
    (combine_exp: (exp -> ('k list * 't list * 'e list) -> 'env -> ('e * 'env))) (env:'env) binders exp : ('e * 'env) =
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
        | Some w -> let w, env = map_exp env b w in Some w, env in
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
  and map_exp env binders (e:'e) = map_exp' map_kind map_typ visit_exp env binders e
  and visit_exp env binders e = 
    let kl, tl, el, env = 
      (match e.v with 
        | Exp_bvar _  
        | Exp_fvar _ 
        | Exp_constant _ -> [], [], [], env
        | Exp_abs(x, t, e) -> 
          let tl, env = map_typs env binders [t] in
          let e, env = map_exp env (push_vbinder binders (Some x)) e in
          [], tl, [e], env
        | Exp_constr_app(_, args) ->
          let args, env = map_either_l env binders args in
          let tl, el = List.fold_left (fun (tl,el) -> function
            | Inl t -> t::tl, el
            | Inr e -> tl, e::el) ([],[]) args in 
          [], List.rev tl, List.rev el, env
        | Exp_tabs(a, k, e) ->
          let k, env = map_kind env binders k in
          let binders = push_tbinder binders (Some a) in
          let e, env = map_exp env binders e in
          [k], [], [e], env
        | Exp_app(e1, e2) -> 
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
            | Pat_var x -> push_vbinder b (Some x)
            | Pat_tvar t -> push_tbinder b (Some t)
            | Pat_cons(c, pats) -> List.fold_left pat_binders b pats
            | Pat_disj(p::_) -> pat_binders b p in
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
        | Exp_let(false, [(x,t,e1)], e2) -> 
          let tl, env = map_typs env binders [t] in
          let el, env = map_exps_with_binders env [(binders, e1); (push_vbinder binders (Some x), e2)] in 
          [], tl, el, env 
        | Exp_let(true, bvdt_tl, e) ->
          let tl = List.map (fun (_, t, _) -> t) bvdt_tl in
          let el = List.map (fun (_, _, e) -> e) bvdt_tl in
          let tl, env = map_typs env binders tl in
          let binders = List.fold_left (fun binders (x, _, _) -> push_vbinder binders (Some x)) binders bvdt_tl in 
          let el, env = map_exps env binders (el@[e]) in
          [], tl, el, env 
        | Exp_primop(_, el) ->
          let el, env = map_exps env binders el in
          [], [], el, env) in
    combine_exp e (kl, tl, el) env in
  map_exp env binders exp
    
let combine_kind k (kl, tl, el) env = 
  let k' = match k(* .u *) with 
    | Kind_star 
    | Kind_prop
    | Kind_erasable
    | Kind_unknown -> k
    | Kind_tcon (aopt, k1, k2) -> let [k1;k2] = kl in Kind_tcon(aopt, k1, k2)
    | Kind_dcon (xopt, t, k) -> Kind_dcon(xopt, List.hd tl, List.hd kl) in
  k', env
    
let combine_typ t (kl, tl, el) env =
  let t' = match compress t with 
    | Typ_unknown
    | Typ_btvar _   
    | Typ_const _ -> t
    | Typ_lam(x, t1, t2) -> let [t1';t2'] = tl in Typ_lam(x, t1', t2')
    | Typ_app(t1, t2) -> let [t1';t2'] = tl in Typ_app(t1',t2')
    | Typ_refine(x, t1, t2) -> let [t1';t2'] = tl in Typ_refine(x, t1', t2')
    | Typ_fun(x, t1, t2) -> let [t1';t2'] = tl in Typ_fun(x, t1', t2')
    | Typ_tlam(a, k, t) -> Typ_tlam(a, List.hd kl, List.hd tl)
    | Typ_univ(a, k, t) -> 
      Typ_univ(a, List.hd kl, List.hd tl)
    | Typ_dep(t, e) -> Typ_dep(List.hd tl, List.hd el)
    | Typ_uvar(x, k) -> Typ_uvar(x, List.hd kl)
    | Typ_ascribed(_,_) -> Typ_ascribed(List.hd tl, List.hd kl) 
    | Typ_meta(Meta_pos(_,r)) -> Typ_meta(Meta_pos(List.hd tl, r))
    | Typ_meta(Meta_tid _) -> t
    | Typ_meta(Meta_cases _) -> Typ_meta(Meta_cases tl) 
    | Typ_meta(Meta_pattern _) -> Typ_meta(Meta_pattern(List.hd tl, (List.tl tl |> List.map Inl)@(el |> List.map Inr))) in
  t', env

let combine_exp e (kl,tl,el) env = 
  let e' = match e.v with 
    | Exp_bvar _  
    | Exp_fvar _ 
    | Exp_constant _ -> e.v
    | Exp_constr_app(v, args) -> 
      let rec reconstruct args tl el = match args, tl, el with
        | (Inl _::args), (t::tl), _ -> Inl t::reconstruct args tl el 
        | Inr _::args, _, e::el_ -> Inr e::reconstruct args tl el 
        | [], [], [] -> []
        | _ -> failwith "Unexpected structure when reconstructing match" in
      let args' = reconstruct args tl el in
      Exp_constr_app(v, args')
    | Exp_abs(x, t, e) -> Exp_abs(x, List.hd tl, List.hd el)
    | Exp_tabs(a, k, e) -> Exp_tabs(a, List.hd kl, List.hd el)
    | Exp_app(e1, e2) -> let [e1';e2'] = el in Exp_app(e1', e2')  
    | Exp_tapp(e, t) -> Exp_tapp(List.hd el, List.hd tl)
    | Exp_match(e1, eqns) -> 
      let e1'::el = el in 
      let rec mk_eqns eqns el = match eqns, el with 
        | (p,None, _)::eqns', e::el' -> (p, None, e)::mk_eqns eqns' el'
        | (p,Some _, _)::eqns', w::e::el' -> (p, Some w, e)::mk_eqns eqns' el'
        | _ -> raise Impos in
      Exp_match(e1', mk_eqns eqns el)
    | Exp_ascribed(e, t) -> Exp_ascribed(List.hd el, List.hd tl)
    | Exp_let(x, bvdt_tl, e) ->
      let el, [e'] = Util.first_N (List.length bvdt_tl) el in
      let bvdt_tl' = List.map3 (fun (bvd, _, _) t e -> (bvd, t, e)) bvdt_tl tl el in
      Exp_let(x, bvdt_tl', e') 
    | Exp_primop(x, es) -> Exp_primop(x, el) in
  withinfo e' e.sort e.p, env

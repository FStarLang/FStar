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
module FStar.Absyn.Visit

open FStar
open FStar.Absyn
open FStar.Absyn.Syntax
open FStar.Util

let log s = ()

(* We always have to compress before pattern matching on a term or a
   type. It computes the substitutions at head of the term. *)
let rec compress_typ_aux pos typ = match typ.n with
  | Typ_uvar (uv,k) ->
      begin
        match Unionfind.find uv with
          | Fixed typ -> compress_typ_aux pos typ
          | _ -> typ
      end
  | Typ_delayed(_, m) ->
    (match !m with
      | None -> typ
      | Some t -> let t' = compress_typ_aux pos t in m := Some t'; t')
  | Typ_ascribed(t, _)
  | Typ_meta(Meta_named(t, _)) when pos -> compress_typ_aux pos t
  | Typ_app({n=Typ_uvar(uv, _)}, args) ->
       begin
          match Unionfind.find uv with
            | Fixed t' -> compress_typ_aux pos <| mk_Typ_app(t', args) None typ.pos
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
  //| Exp_ascribed(e, _)
  | Exp_meta(Meta_desugared(e, _)) when meta -> compress_exp_aux meta e
  | Exp_app({n=Exp_uvar(uv, _)}, args) ->
       begin match Unionfind.find uv with
        | Fixed e' -> mk_Exp_app(e', args) None exp.pos
        | _ -> exp
       end
  | _ -> exp
let compress_exp e = compress_exp_aux true e
let compress_exp_uvars e = compress_exp_aux false e

let rec compress_kind knd = match knd.n with
  | Kind_delayed(_, _, m) ->
    (match !m with
      | None -> knd
      | Some k -> let k' = compress_kind k in m := Some k'; k')
  | _ -> knd

let left ext benv btv = match ext benv (Inl btv) with
  | benv, Inl bvd -> benv, bvd
  | _ -> failwith "impossible"
let right ext benv bvv = match ext benv (Inr bvv) with
  | benv, Inr bvd -> benv, bvd
  | _ -> failwith "impossible"

(*************************************************************************************)
(* A general way of reducing types. *)
(*************************************************************************************)
type boundvar = either<btvdef, bvvdef>
type boundvars = list<boundvar>
type imap<'env, 'm> = 'env -> boundvars -> 'm -> ('m * 'env)
type mapper<'env, 'm, 'n> =
    imap<'env,knd>
    -> imap<'env, typ>
    -> imap<'env, exp>
    -> 'env -> boundvars -> 'm -> ('n * 'env)

let push_tbinder binders = function
  | None -> binders
  | Some a -> (Inl a)::binders
let push_vbinder binders = function
  | None -> binders
  | Some a -> (Inr a)::binders
let bvd_to_bvar_s bvd sort = {v=bvd; sort=sort; p=bvd.ppname.idRange}
let tbinder_opt aopt k = match aopt with
    | None -> []
    | Some a -> [Inl (bvd_to_bvar_s a k)]
let vbinder_opt aopt t = match aopt with
    | None -> []
    | Some a -> [Inr (bvd_to_bvar_s a t)]


type knd_components = binders * list<knd> * list<typ> * list<arg>
type typ_components = binders * list<knd> * list<typ> * list<comp> * list<list<arg>>
type exp_components = binders * list<knd> * list<typ> * list<exp> * list<arg>
let leaf_k () = ([], [], [], [])
let leaf_te () = ([], [], [], [], [])

let rec reduce_kind
    (map_kind': mapper<'env, knd, knd>)
    (map_typ': mapper<'env, typ, typ>)
    (map_exp': mapper<'env, exp, exp>)
    (combine_kind: (knd -> knd_components -> 'env -> (knd * 'env)))
    (combine_typ: (typ -> typ_components -> 'env -> (typ * 'env)))
    (combine_exp: (exp -> exp_components -> 'env -> (exp * 'env)))
    (env:'env) binders k: (knd * 'env) =
  let rec visit_kind env binders k : (knd * 'env) =
    let k = compress_kind k in
    let components, env : (knd_components * 'env) =
      match k.n with
        | Kind_delayed _ -> failwith "Impossible"
        | Kind_lam _
        | Kind_type
        | Kind_effect
        | Kind_unknown ->
          leaf_k(), env
        | Kind_uvar(_, args) ->
          let args, env = map_args map_typ map_exp env binders args in
          ([], [], [], args), env
        | Kind_abbrev(kabr, k) ->
          let k, env = map_kind env binders k in
          let args, env = map_args map_typ map_exp env binders (snd kabr) in
          ([], [k], [], args), env
        | Kind_arrow(bs, k) ->
          let bs, binders, env = map_binders map_kind map_typ env binders bs in
          let k, env = map_kind env binders k in
          (bs, [k], [], []), env
    in
    combine_kind k components env
  and map_kind env binders k = map_kind' visit_kind map_typ map_exp env binders k
  and map_typ env binders t = reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t
  and map_exp env binders e = reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e
  in
  map_kind env binders k

and map_args (map_typ:imap<'env, typ>) (map_exp:imap<'env,exp>) (env:'env) binders arguments : (args * 'env) =
    let args', env = List.fold_left (fun (out, env) (arg, imp) ->
        match arg with
        | Inl t ->
            let t, env = map_typ env binders t in
            ((Inl t, imp)::out, env)
        | Inr e ->
            let e, env = map_exp env binders e in
            ((Inr e, imp)::out, env)) ([], env) arguments in
    List.rev args', env

and map_binders (map_kind:imap<'env,knd>) (map_typ:imap<'env,typ>) (env:'env) binders (bs:Syntax.binders) : (Syntax.binders * boundvars * 'env) =
    let bs, binders, env = bs |> List.fold_left (fun (bs, binders, env) b -> match b with
        | Inl a, imp ->
            let k, env = map_kind env binders a.sort in
            let binders = push_tbinder binders (Some a.v) in
            (Inl (bvd_to_bvar_s a.v k), imp)::bs, binders, env

        | Inr x, imp ->
            let t, env = map_typ env binders x.sort in
            let binders = push_vbinder binders (Some x.v) in
            (Inr (bvd_to_bvar_s x.v t), imp)::bs, binders, env) ([], binders, env) in
    List.rev bs, binders, env

and reduce_typ
    (map_kind': mapper<'env, knd, knd>)
    (map_typ': mapper<'env, typ, typ>)
    (map_exp': mapper<'env, exp, exp>)
    (combine_kind: (knd -> knd_components -> 'env -> (knd * 'env)))
    (combine_typ: (typ -> typ_components -> 'env -> (typ * 'env)))
    (combine_exp: (exp -> exp_components -> 'env -> (exp * 'env)))
    (env:'env) binders t : (typ * 'env) =

  let rec map_comp (env:'env) (binders:list<either<btvdef,bvvdef>>) (c:comp) =
    match c.n with
    | Total t ->
      let t, env = map_typ env binders t in
      mk_Total t, env
    | Comp ct ->
      let t, env = map_typ env binders ct.result_typ in
      let args, env = map_args map_typ map_exp env binders ct.effect_args in
      let env, flags = ct.flags |> Util.fold_map (fun env flag -> match flag with
        | DECREASES arg -> let arg, env = map_exp env binders arg in env, DECREASES arg
        | f -> env, f) env in
      mk_Comp ({ct with result_typ=t; effect_args=args; flags=flags}), env

  and visit_typ env binders t : (typ * 'env) =
    let components, env = match (compress_typ t).n with
      | Typ_delayed _ -> failwith "Impossible"
      | Typ_unknown
      | Typ_btvar _
      | Typ_const _ ->
        let _, env = map_typ env binders t in
        leaf_te(), env

      | Typ_app(t, args) ->
        let t, env = map_typ env binders t in
        let args, env = map_args map_typ map_exp env binders args in
        ([], [], [t], [], [args]), env

      | Typ_lam(axs, t) ->
        let axs, binders, env = map_binders map_kind map_typ env binders axs in
        let t, env = map_typ env binders t in
        (axs, [], [t], [], []), env

      | Typ_refine(x, t2) ->
        let bs, binders, env = map_binders map_kind map_typ env binders [Inr x, None] in
        let t2, env = map_typ env binders t2 in
        (bs, [], [t2], [], []), env

      | Typ_fun(bs, c) ->
        let bs, binders, env = map_binders map_kind map_typ env binders bs in
        let c, env = map_comp env binders c in
        (bs, [], [], [c], []), env

      | Typ_ascribed(t,k) ->
        let t, env = map_typ env binders t in
        let k, env = map_kind env binders k in
        ([], [k], [t], [], []), env

      | Typ_uvar(_, k) ->
        let k, env = map_kind env binders k in
        ([], [k], [], [], []), env

      | Typ_meta(Meta_slack_formula(t1, t2, flag)) ->
        let t1, env = map_typ env binders t1 in
        let t2, env = map_typ env binders t2 in
        ([], [], [t1;t2], [], []), env

      | Typ_meta(Meta_labeled(t, _, _, _))
      | Typ_meta(Meta_named(t, _))
      | Typ_meta(Meta_refresh_label(t, _, _)) ->
        let t, env = map_typ env binders t in
        ([], [], [t], [], []), env

      | Typ_meta(Meta_pattern(t,ps)) ->
        let t,env = map_typ env binders t in
        let map_pats env pats : list<arg> * 'env = 
            let pats, env = List.fold_left (fun (pats, env) arg -> match arg with
              | Inl t, _ -> let t, env = map_typ env binders t in ((Inl t, None)::pats, env)
              | Inr e, _ -> let e, env = map_exp env binders e in ((Inr e, None)::pats, env)) ([], env) pats in
            List.rev pats, env in 
        let pats, env = List.fold_left (fun (out, env) pats -> let pats, env = map_pats env pats in (pats::out, env)) ([], env) ps in
        ([], [], [t], [], List.rev pats), env in

    combine_typ t components env

  and map_kind env binders k = reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k
  and map_typ env binders t = map_typ' map_kind visit_typ map_exp env binders t
  and map_exp env binders e = reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e
  in
  map_typ env binders t

and reduce_exp
    (map_kind': mapper<'env, knd, knd>)
    (map_typ': mapper<'env, typ, typ>)
    (map_exp': mapper<'env, exp, exp>)
    (combine_kind: (knd -> knd_components -> 'env -> (knd * 'env)))
    (combine_typ: (typ -> typ_components -> 'env -> (typ * 'env)))
    (combine_exp: (exp -> exp_components -> 'env -> (exp * 'env)))
    (env:'env) binders e : (exp * 'env) =
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
  and map_kind env binders k = reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k
  and map_typ env binders t = reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t
  and map_exp env binders e = map_exp' map_kind map_typ visit_exp env binders e
  and visit_exp env binders e : (exp * 'env) =
     let e = compress_exp_uvars e in
     let components, env = match e.n with
        | Exp_delayed _ -> failwith "impossible"

        | Exp_meta(Meta_desugared(e, _)) ->
          let e, env = map_exp env binders e in
          ([], [], [], [e], []), env

        | Exp_bvar _
        | Exp_fvar _
        | Exp_constant _ ->
          leaf_te(), env

        | Exp_uvar(_, t) ->
          let t, env = map_typ env binders t in
          ([], [], [t], [], []), env

        | Exp_abs(bs, e) ->
          let bs, binders, env = map_binders map_kind map_typ env binders bs in
          let e, env = map_exp env binders e in
          (bs, [], [], [e], []), env

        | Exp_app(e, args) ->
          let e, env = map_exp env binders e in
          let args, env = map_args map_typ map_exp env binders args in
          ([], [], [], [e], args), env

        | Exp_match(e1, pl) ->
          let rec pat_binders b p = match p.v with
            | Pat_dot_term _
            | Pat_dot_typ _
            | Pat_wild _
            | Pat_twild _
            | Pat_constant _ -> b
            | Pat_var x -> push_vbinder b (Some x.v)
            | Pat_tvar t -> push_tbinder b (Some t.v)
            | Pat_cons(_, _, pats) -> List.fold_left (fun b (p, _) -> pat_binders b p) b pats
            | Pat_disj(p::_) -> pat_binders b p
            | Pat_disj [] -> failwith "impossible" in
          let branches = pl |> List.collect (fun (p,w,e) ->
            let binders = pat_binders binders p in
            match w with
              | None -> [(binders, e)]
              | Some w -> [(binders, w); (binders, e)]) in
          let el, env = map_exps_with_binders env ((binders, e1)::branches) in
          ([], [], [], el, []), env

        | Exp_ascribed(e, t, _) ->
          let t, env = map_typ env binders t in
          let e, env = map_exp env binders e in
          ([], [], [t], [e], []), env

        | Exp_let((false, [lb]), e2) ->
          let t, env = map_typ env binders lb.lbtyp in
          let binders' = match lb.lbname with
            | Inl x -> push_vbinder binders (Some x)
            | _ -> binders in
          let el, env = map_exps_with_binders env [(binders, lb.lbdef); (binders', e2)] in
          ([], [], [t], el, []), env

        | Exp_let((true, bvdt_tl), e) ->
          let tl = List.map (fun lb -> lb.lbtyp) bvdt_tl in
          let el = List.map (fun lb -> lb.lbdef) bvdt_tl in
          let tl, env = tl |> List.fold_left (fun (tl, env) t ->
            let t, env = map_typ env binders t in
            t::tl, env) ([], env) in
          let tl = List.rev tl in
          let binders = List.fold_left (fun binders lb -> match lb.lbname with
            | Inl x -> push_vbinder binders (Some x)
            | _ -> binders) binders bvdt_tl in
          let el, env = map_exps env binders (el@[e]) in
          ([], [], tl, el, []), env

        | Exp_let _ -> failwith "impossible"
    in
    combine_exp e components env in
  map_exp env binders e

let combine_kind k (kc:knd_components) env =
  let k' = match k.n, kc with
    | Kind_lam _, _
    | Kind_type, _
    | Kind_effect, _
    | Kind_unknown, _ ->                         (fun p -> Util.return_all k) //need an effect coercion here
    | Kind_uvar(u, _), (_, _, _, args) ->        mk_Kind_uvar(u, args)
    | Kind_abbrev(kabr, _), (_, [k], _, args) -> mk_Kind_abbrev((fst kabr, args), k)
    | Kind_arrow(_, _), (bs, [k'], _ , _)  ->    mk_Kind_arrow(bs, k')
    | _ -> failwith "impossible" in
  k' k.pos, env

let combine_typ t (tc:typ_components) env =
  let t = compress_typ t in
  let w f = f None t.pos in
  let t' = match t.n, tc with
    | Typ_unknown, _
    | Typ_btvar _, _
    | Typ_const _, _ -> t
    | Typ_lam _, (bs, _, [t], _, _) ->                             w <| mk_Typ_lam(bs, t)
    | Typ_app _, (_, _, [t], _, [args]) ->                           w <| mk_Typ_app(t, args)
    | Typ_refine _, ([(Inr x, _)], _, [t], _, _) ->                w <| mk_Typ_refine(x, t)
    | Typ_fun _, (bs, _, _, [c], _) ->                             w <| mk_Typ_fun(bs, c)
    | Typ_uvar(x, _), (_, [k], _, _, _) ->                         w <| mk_Typ_uvar'(x, k)
    | Typ_ascribed _, (_, [k], [t], _, _) ->                       w <| mk_Typ_ascribed'(t, k)
    | Typ_meta(Meta_named(_, l)), (_, _, [t'], _, _) ->            w <| mk_Typ_meta'(Meta_named(t', l))
    | Typ_meta(Meta_pattern _), (_, _, [t], _, args) ->            w <| mk_Typ_meta'(Meta_pattern(t, args))
    | Typ_meta(Meta_labeled(_, l, r, p)), (_, _, [t], _, _) ->        w <| mk_Typ_meta'(Meta_labeled(t, l, r, p))
    | Typ_meta(Meta_refresh_label(_, b, r)), (_, _, [t], _, _)  -> w <| mk_Typ_meta'(Meta_refresh_label(t, b, r))
    | Typ_meta(Meta_slack_formula(_, _, _)), (_, _, [t1;t2], _, _) -> w <| mk_Typ_meta'(Meta_slack_formula(t1, t2, Util.mk_ref false))
    | _ -> failwith "impossible" in
  t', env

let combine_exp e (ec:exp_components) env =
  let e = compress_exp e in
  let w f = f None e.pos in
  let e' = match e.n, ec with
    | Exp_bvar _, _
    | Exp_fvar _, _
    | Exp_constant _, _ -> e
    | Exp_uvar(uv, _), (_, _, [t], _, _) ->                  w <| mk_Exp_uvar'(uv, t)
    | Exp_abs _, (bs, _, _, [e], _)  ->                      w <| mk_Exp_abs(bs, e)
    | Exp_app _, (_, _, _, [e], args) ->                     w <| mk_Exp_app(e, args)
    | Exp_ascribed (_,_,l), (_, _, [t], [e], _) ->           w <| mk_Exp_ascribed(e, t, l)
    | Exp_meta(Meta_desugared(_, tag)), (_, _, _, [e], _) -> w <| mk_Exp_meta' (Meta_desugared(e, tag))
    | Exp_match (_, eqns), (_, [], [], e1::el, _) ->
      let rec mk_eqns eqns el = match eqns, el with
        | (p,None, _)::eqns', e::el' -> (p, None, e)::mk_eqns eqns' el'
        | (p,Some _, _)::eqns', w::e::el' -> (p, Some w, e)::mk_eqns eqns' el'
        | [], [] -> []
        | _ -> failwith "impossible" in
                                                             w <| mk_Exp_match(e1, mk_eqns eqns el)
    | Exp_let((is_rec, lbs), _), (_, _, tl, el, _) ->
      begin match Util.first_N (List.length lbs) el with
        | el, [e'] ->
          let lbs' = List.map3 (fun lb t e -> {lb with lbtyp=t; lbdef=e}) lbs tl el in
          w <| mk_Exp_let((is_rec, lbs'), e')
        | _ -> failwith "impossible"
      end

    | _ -> failwith "impossible" in
  e', env

let collect_from_typ (f:'env -> typ -> 'env) (env:'env) (t:typ) : 'env =
   snd <| reduce_typ (fun _ _ _ env _ k -> k, env)
                     (fun _ vt _ env bvs t ->
                        let env = f env t in
                        match (compress_typ t).n with
                          | Typ_unknown
                          | Typ_btvar _
                          | Typ_const _ -> t, env
                          | _ -> vt env bvs t)
                     (fun _ _ _ env _ e -> e, env)
                     (fun k _ env -> k, env)
                     (fun t _ env -> t, env)
                     (fun e _ env -> e, env)
                     env
                     []
                     t

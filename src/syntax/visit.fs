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
module FStar.Syntax.Visit

open FStar
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Util

(*
    force_uvar (pos:bool) (t:term) 
        replaces any unification variable at the head of t
        with the term that it has been fixed to, if any.

        when pos is true, it also removes any ascriptions 
        or Meta_named constructors at the head of t 
*)
let rec force_uvar_aux pos t = match t.n with
  | Tm_uvar (uv,_) ->
      begin
        match Unionfind.find uv with
          | Fixed t' -> force_uvar_aux pos t'
          | _ -> t
      end
  | Tm_delayed(f, m) ->
    (match !m with
      | None -> 
        begin match f with 
            | Inr c -> let t' = force_uvar_aux pos (c()) in m := Some t'; t'
            | _ -> t
        end
      | Some t' -> let t' = force_uvar_aux pos t' in m := Some t'; t')
  | Tm_ascribed(t, _, _)
  | Tm_meta(Meta_named(t, _)) when pos -> force_uvar_aux pos t
  | Tm_app({n=Tm_uvar(uv, _)}, args) ->
       begin
          match Unionfind.find uv with
            | Fixed t' -> force_uvar_aux pos (mk (Tm_app(t', args)) None t.pos)
            | _ -> t
       end
  | _ -> t
let force_uvar_and_ascriptions = force_uvar_aux true
let force_uvar = force_uvar_aux false 

let left ext benv btv = match ext benv (Inl btv) with
  | benv, Inl bvd -> benv, bvd
  | _ -> failwith "impossible"
let right ext benv bvv = match ext benv (Inr bvv) with
  | benv, Inr bvd -> benv, bvd
  | _ -> failwith "impossible"

(*************************************************************************************)
(* A general way of reducing types. *)
(*************************************************************************************)
type imap<'env, 'm> = 'env -> 'm -> ('m * 'env)
type mapper<'env> = imap<'env, term> -> imap<'env,term>
type tm_components = list<universe> * binders * list<term> * list<comp> * list<arg>
let rec reduce
    (map': mapper<'env>)
    (combine: (term -> list<tm_components> -> 'env -> (term * 'env)))
    (env:'env) t : (term * 'env) =
  let rec visit env t : (term * 'env) =
    let t = force_uvar t in
    let components, env : (list<tm_components> * 'env) =
      match t.n with
        | Tm_delayed _ -> failwith "Impossible"
        
        | Tm_bvar(_, us)
        | Tm_name(_, us)
        | Tm_fvar(_, us) -> 
          let _, env = map env t in
          [us, [], [], [], []], env 

        | Tm_meta(Meta_unknown)
        | Tm_constant _ -> 
          let _, env = map env t in 
          [], env 

        | Tm_type u -> 
          let _, env = map env t in 
          [[u], [], [], [], []], env

        | Tm_abs(binders, t) -> 
          let binders, env = map_binders map env binders in 
          let t, env = map env t in 
          [[], binders, [t], [], []], env

        | Tm_arrow(binders, comp) -> 
          let binders, env = map_binders map env binders in 
          let comp, env = map_comp map env comp in 
          [[], binders, [], [comp], []], env      

        | Tm_refine(bv, t) -> 
          let binders, env = map_binders map env [(bv, None)] in
          let t, env = map env t in 
          [[], binders, [t], [], []], env

        | Tm_app(t, args) -> 
          let args, env = map_args map env args in
          let t, env = map env t in 
          [[], [], [t], [], args], env

        | Tm_match(t, branches) -> 
          let rec pat_binders b p = match p.v with
            | Pat_dot_term _
            | Pat_wild _
            | Pat_constant _ -> b
            | Pat_var x -> (x, None)::b
            | Pat_cons(_, pats) -> List.fold_left (fun b (p, _) -> pat_binders b p) b pats
            | Pat_disj(p::_) -> pat_binders b p
            | Pat_disj [] -> failwith "impossible" in
          let components, env = branches |> List.fold_left (fun (components, env) (p,w,e) ->
            let binders = pat_binders [] p in
            let binders, env = map_binders map env binders in 
            let wopt, env = match w with 
                | None -> [], env
                | Some w -> let w, env = map env w in [w], env in
            let e, env = map env e in
            let tms = e::wopt in
            ([], binders, tms, [], [])::components, env) ([], env) in
          List.rev components, env

        | Tm_ascribed(t1, t2, opt) -> 
          let t1, env = map env t1 in 
          let t2, env = map env t2 in 
          [[], [], [t1;t2], [], []], env
        
        | Tm_let(lbs, t) -> 
          let components, env =
            snd lbs |> List.fold_left (fun (components, env) lb -> 
                let t, env = map env lb.lbtyp in 
                let e, env = map env lb.lbdef in
                ([], [], [t;e], [], [])::components, env) ([], env) in
          let t, env = map env t in 
          ([], [], [t], [], [])::List.rev components, env

        | Tm_uvar(_, t) -> 
          let t, env = map env t in 
          [[], [], [t], [], []], env    
          

        | Tm_meta(Meta_labeled(t, _, _, _))
        | Tm_meta(Meta_named(t, _))
        | Tm_meta(Meta_refresh_label(t, _, _))
        | Tm_meta(Meta_desugared(t, _)) ->
          let t, env = map env t in
          [[], [], [t], [], []], env

        | Tm_meta(Meta_pattern(t,ps)) ->
          let t,env = map env t in
          let args,env = map_args map env ps in 
          [[], [], [t], [], args], env

    in
    combine t components env
  and map env t = map' visit env t in
  map env t

and map_args (map:imap<'env, term>) (env:'env) (arguments:args) : (args * 'env) =
    let args', env = List.fold_left (fun (out, env) (arg, imp) ->
        let t, env = map env arg in 
        (t, imp)::out, env) ([], env) arguments in
    List.rev args', env

and map_binders (map:imap<'env,term>) (env:'env) (bs:Syntax.binders) : (Syntax.binders * 'env) =
    let bs, env = bs |> List.fold_left (fun (bs, env) (a, imp) ->
        let t, env = map env a.sort in 
        ({a with sort=t},imp)::bs, env) ([], env) in
    List.rev bs, env
   
and map_comp (map:imap<'env,term>) (env:'env) (c:comp) =
    match c.n with
    | Total t ->
      let t, env = map env t in
      mk_Total t, env
    | Comp ct ->
      let t, env = map env ct.result_typ in
      let args, env = map_args map env ct.effect_args in
      let env, flags = ct.flags |> Util.fold_map (fun env flag -> match flag with
        | DECREASES arg -> let arg, env = map env arg in env, DECREASES arg
        | f -> env, f) env in
      mk_Comp ({ct with result_typ=t; effect_args=args; flags=flags}), env


let combine e (ec:list<tm_components>) env =
  let e = force_uvar e in
  let mk f = Syntax.mk f None e.pos in
  let e' = match e.n, ec with
    | Tm_bvar _, _
    | Tm_fvar _, _
    | Tm_name _, _
    | Tm_constant _, _
    | Tm_meta(Meta_unknown), _
    | Tm_type _, _ -> e
    
    | Tm_abs(_, _), [_, bs, [t], _, _] -> 
      mk (Tm_abs(bs, t))

    | Tm_arrow(_, _), [_, bs, _, [c], _] -> 
      mk (Tm_arrow(bs, c))

    | Tm_refine(_, _), [_, [b], [t], _, _] -> 
      mk (Tm_refine(fst b, t))

    | Tm_app(_, _), [_, _, [t], _, args] -> 
      mk (Tm_app(t, args))

    | Tm_match(_, pats), (_, _, [t], _, _)::pats' -> 
      if List.length pats <> List.length pats'
      then failwith "Impossible";
      let remap_pat_binders p b = failwith "remap_pat_binders" in
      let pats = List.map2 (fun (p, w, e) (_, binders, tms, _, _) -> 
       let p = remap_pat_binders p binders in 
       let w, e = match w, tms with 
        | None, [e] -> None, e
        | Some _, [e; w] -> Some w, e
        | _ -> failwith "Impossible" in 
       p, w, e) pats pats' in 
      mk (Tm_match(t, pats))

    | Tm_ascribed(_, _, l), [_, _, [t1; t2], _, _] ->
      mk (Tm_ascribed(t1, t2, l))

    | Tm_let((b,lbs), _), (_, _, [t], _, _)::lbs' -> 
      let lbs = List.map2 (fun lb -> function 
        | (_, _, [t1; t2], _, _) -> {lb with lbtyp=t1; lbdef=t2}
        | _ -> failwith "Impossible") lbs lbs' in 
      mk (Tm_let((b,lbs), t))
  
    | Tm_uvar(uv, _), [_, _, [t], _, _] -> 
      mk (Tm_uvar(uv, t))

    | Tm_delayed _, _ -> failwith "Impossible"

    | Tm_meta(Meta_named(_, l)), [_, _, [t], _, _] ->             mk <| Tm_meta(Meta_named(t, l))
    | Tm_meta(Meta_pattern _), [_, _, [t], _, args] ->            mk <| Tm_meta(Meta_pattern(t, args))
    | Tm_meta(Meta_labeled(_, l, r, p)), [_, _, [t], _, _] ->     mk <| Tm_meta(Meta_labeled(t, l, r, p))
    | Tm_meta(Meta_refresh_label(_, b, r)), [_, _, [t], _, _]  -> mk <| Tm_meta(Meta_refresh_label(t, b, r))
    | Tm_meta(Meta_desugared(_, tag)), [_, _, [t], _, _] ->       mk <| Tm_meta(Meta_desugared(t, tag))
    
    | _ -> failwith "Impossible" in
   e', env
    
let collect_from_typ (f:'env -> term -> 'env) (env:'env) (t:typ) : 'env =
   snd <| reduce (fun v env (t:term) ->
                        let env = f env t in
                        match (force_uvar t).n with
                          | Tm_meta Meta_unknown
                          | Tm_bvar _
                          | Tm_constant _ -> t, env
                          | _ -> v env t)
                  (fun t _ env -> t, env)
                  env
                  t

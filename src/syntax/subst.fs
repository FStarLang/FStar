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
module FStar.Syntax.Subst

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
  | Tm_meta(t, Meta_named _) when pos -> force_uvar_aux pos t
  | Tm_app({n=Tm_uvar(uv, _)}, args) ->
       begin
          match Unionfind.find uv with
            | Fixed t' -> force_uvar_aux pos (mk (Tm_app(t', args)) None t.pos)
            | _ -> t
       end
  | _ -> t
let force_uvar_and_ascriptions = force_uvar_aux true
let force_uvar = force_uvar_aux false 

(********************************************************************************)
(*************************** Delayed substitutions ******************************)
(********************************************************************************)
let subst_to_string s = s |> List.map (fun (b, _) -> b.ppname.idText) |> String.concat ", "

let subst_bv s a = Util.find_map s (function DB (i, t) when i=a.index -> Some t | _ -> None)
let subst_nm s a = Util.find_map s (function NM (x, i) when bv_eq a x -> Some (bv_to_tm ({x with index=i})) | _ -> None)
let rec subst' (s:subst_t) t = match s with
  | [] 
  | [[]] -> force_uvar t
  | _ ->
    let t0 = force_uvar t in
    let rec aux f a s = match s with
        | [] -> t0
        | s0::rest ->
          match f s0 a with
            | Some t  -> subst' rest t
            | _ -> aux f a rest in

    match t0.n with
        | Tm_delayed(Inl(t', s'), m) ->
            mk (Tm_delayed (Inl (t', s@s'), Util.mk_ref None))
                None
                t.pos

        | Tm_delayed(Inr _, _) -> 
          failwith "Impossible: Visit.force_uvar removes lazy delayed nodes"

        | Tm_bvar a ->
          aux subst_bv a s

        | Tm_name a -> 
          aux subst_nm a s

        | Tm_constant _
        | Tm_uvar _
        | Tm_fvar _ -> t0

        | _ -> mk (Tm_delayed(Inl(t0, s), Util.mk_ref None))
                   None
                   t.pos

and subst_flags' s flags =
    flags |> List.map (function
        | DECREASES a -> DECREASES (subst' s a)
        | f -> f)

and subst_comp_typ' s t = match s with
  | []
  | [[]] -> t
  | _ ->
    {t with result_typ=subst' s t.result_typ;
            flags=subst_flags' s t.flags;
            effect_args=List.map (fun (t, imp) -> subst' s t, imp) t.effect_args}

and subst_comp' s t = match s with
  | []
  | [[]] -> t
  | _ ->
    match t.n with
      | Total t -> mk_Total (subst' s t)
      | Comp ct -> mk_Comp(subst_comp_typ' s ct)

and compose_subst (s1:subst_t) (s2:subst_t) = s1@s2

let shift n = function 
    | DB(i, t) -> DB(i+n, t)
    | NM(x, i) -> NM(x, i+n)
let shift_subst' n s = s |> List.map (List.map (shift n))
let subst_binder' s (x:bv, imp) = {x with sort=subst' s x.sort}, imp
let subst_binders' s bs = 
    bs |> List.mapi (fun i b -> 
        if i=0 then subst_binder' s b
        else subst_binder' (shift_subst' i s) b)
let subst_arg' s (t, imp) = (subst' s t, imp)
let subst_args' s = List.map (subst_arg' s)
let subst_pat' s pat : (pat * int) = 
    let rec aux n pat : (pat * int) = match pat.v with 
      | Pat_disj [] -> failwith "Impossible: empty disjunction"
     
      | Pat_constant _ -> pat, n

      | Pat_disj(p::ps) -> 
        let p, m = aux n pat in
        let ps = List.map (fun p -> fst (aux n p)) ps in
        {pat with v=Pat_disj(p::ps)}, m

      | Pat_cons(fv, pats) ->
        let pats, n = pats |> List.fold_left (fun (pats, n) (p, imp) -> 
            let p, m = aux n p in
            ((p,imp)::pats, m)) ([], n) in
        {pat with v=Pat_cons(fv, List.rev pats)}, n

      | Pat_var x ->
        let s = shift_subst' n s in 
        let x = {x with sort=subst' s x.sort} in
        {pat with v=Pat_var x}, n + 1

      | Pat_wild x -> 
        let s = shift_subst' n s in 
        let x = {x with sort=subst' s x.sort} in
        {pat with v=Pat_var x}, n //these are not in scope, so don't shift the index

      | Pat_dot_term(x, t0) -> 
        let s = shift_subst' n s in
        let x = {x with sort=subst' s x.sort} in
        let t0 = subst' s t0 in 
        {pat with v=Pat_dot_term(x, t0)}, n //these are not in scope, so don't shift the index
  in aux 0 pat

let push_subst s t = 
    let t = force_uvar t in 
    match t.n with 
        | Tm_delayed _ -> failwith "Impossible"

        | Tm_uvar _ 
        | Tm_constant _
        | Tm_fvar _
        | Tm_type _ 
        | Tm_unknown -> t

        | Tm_bvar _ 
        | Tm_name _  -> subst' s t

        | Tm_uinst(t', us) -> //t must be a variable
          let t' = subst' s t' in
          begin match t'.n with
            | Tm_bvar _
             | Tm_name _
            | Tm_fvar _ -> //it remains a variable
              mk (Tm_uinst(t, us)) None t'.pos
            | _ -> 
              //no longer a variable; this can only happend as we're reducing a let binding
              //universe instantiation is discarded as we reduce
              t'
          end

        | Tm_app(t0, args) -> mk (Tm_app(subst' s t0, subst_args' s args)) None t.pos
        | Tm_ascribed(t0, t1, lopt) -> mk (Tm_ascribed(subst' s t0, subst' s t1, lopt)) None t.pos
         

        | Tm_abs(bs, body) -> 
          let n = List.length bs in 
          mk (Tm_abs(subst_binders' s bs, subst' (shift_subst' n s) body)) None t.pos   
          
        | Tm_arrow(bs, comp) -> 
          let n = List.length bs in 
          mk (Tm_arrow(subst_binders' s bs, subst_comp' (shift_subst' n s) comp)) None t.pos   
        
        | Tm_refine(x, phi) -> 
          let x = {x with sort=subst' s x.sort} in
          let phi = subst' (shift_subst' 1 s) phi in
          mk (Tm_refine(x, phi)) None t.pos

        | Tm_match(t0, pats) -> 
          let t0 = subst' s t0 in
          let pats = pats |> List.map (fun (pat, wopt, branch) -> 
            let pat, n = subst_pat' s pat in 
            let s = shift_subst' n s in 
            let wopt = match wopt with 
                | None -> None
                | Some w -> Some (subst' s w) in
            let branch = subst' s branch in 
            (pat, wopt, branch)) in
          mk (Tm_match(t0, pats)) None t.pos    
           
        | Tm_let((is_rec, lbs), body) -> 
          let n = List.length lbs in
          let sn = shift_subst' n s in
          let body = subst' sn body in 
          let lbs = lbs |> List.map (fun lb -> 
            let lbt = subst' s lb.lbtyp in
            let lbd = if is_rec && Util.is_left (lb.lbname) //if it is a recursive local let, then all the let bound names are in scope for the body
                      then subst' sn lb.lbdef 
                      else subst' s lb.lbdef in
            {lb with lbtyp=lbt; lbdef=lbd}) in
          mk (Tm_let((is_rec, lbs), body)) None t.pos  
         
        | Tm_meta(t0, Meta_pattern ps) -> 
          mk (Tm_meta(subst' s t0, Meta_pattern (subst_args' s ps))) None t.pos

        | Tm_meta(t, m) -> 
          mk (Tm_meta(subst' s t,  m)) None t.pos 

let rec compress (t:term) = 
    let t = force_uvar t in 
    match t.n with 
        | Tm_delayed(Inl(t, s), memo) -> 
          let t' = compress (push_subst s t) in
          memo := Some t';
          t'
        | _ -> t
            
let subst s t = subst' [s] t
let subst_comp s t = subst_comp' [s] t

(*************************************************************************************)
(* A general way of reducing types. *)
(*************************************************************************************)
type imap<'env> = 'env -> term -> (term * 'env)
type mapper<'env> = imap<'env> -> imap<'env>
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
        
        | Tm_bvar _
        | Tm_name _
        | Tm_fvar _ -> 
          let _, env = map env t in
          [], env 
    
        | Tm_uinst (t, us) -> 
          let t, env = map env t in 
          [us, [], [t], [], []], env

        | Tm_unknown
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
         
        | Tm_meta(t, Meta_pattern ps) ->
          let t,env = map env t in
          let args,env = map_args map env ps in 
          [[], [], [t], [], args], env

        | Tm_meta(t, _) ->
          let t, env = map env t in
          [[], [], [t], [], []], env

    in
    combine t components env
  and map env t = map' visit env t in
  map env t

and map_args (map:imap<'env>) (env:'env) (arguments:args) : (args * 'env) =
    let args', env = List.fold_left (fun (out, env) (arg, imp) ->
        let t, env = map env arg in 
        (t, imp)::out, env) ([], env) arguments in
    List.rev args', env

and map_binders (map:imap<'env>) (env:'env) (bs:Syntax.binders) : (Syntax.binders * 'env) =
    let bs, env = bs |> List.fold_left (fun (bs, env) (a, imp) ->
        let t, env = map env a.sort in 
        ({a with sort=t},imp)::bs, env) ([], env) in
    List.rev bs, env
   
and map_comp (map:imap<'env>) (env:'env) (c:comp) =
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
    | Tm_unknown, _
    | Tm_type _, _ -> e
    
    | Tm_uinst(_, _), [us, [], [t], [], []] -> 
      mk (Tm_uinst(t, us))

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

    | Tm_meta(_, Meta_pattern _), [_, _, [t], _, args] ->            
      mk <| Tm_meta(t, Meta_pattern args)
    
    | Tm_meta(_, m), [_, _, [t], _, _] ->             
      mk <| Tm_meta(t, m)

    | _ -> failwith "Impossible" in
   e', env
    
let collect_from_typ (f:'env -> term -> 'env) (env:'env) (t:typ) : 'env =
   snd <| reduce (fun v env (t:term) ->
                        let env = f env t in
                        match (force_uvar t).n with
                          | Tm_unknown
                          | Tm_bvar _
                          | Tm_constant _ -> t, env
                          | _ -> v env t)
                  (fun t _ env -> t, env)
                  env
                  t


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
    force_uvar (t:term) 
        replaces any unification variable at the head of t
        with the term that it has been fixed to, if any.
*)
let rec force_uvar t = match t.n with
  | Tm_uvar (uv,_) ->
      begin
        match Unionfind.find uv with
          | Fixed t' -> force_uvar t'
          | _ -> t
      end
  | _ -> t

let rec force_delayed_thunk t = match t.n with
  | Tm_delayed(f, m) ->
    (match !m with
      | None -> 
        begin match f with 
            | Inr c -> let t' = force_delayed_thunk (c()) in m := Some t'; t'
            | _ -> t
        end
      | Some t' -> let t' = force_delayed_thunk t' in m := Some t'; t')
  | _ -> t

let rec compress_univ u = match u with 
    | U_unif u' -> 
      begin match Unionfind.find u' with 
        | Some u -> compress_univ u
        | _ -> u
      end
    | _ -> u
    
(********************************************************************************)
(*************************** Delayed substitutions ******************************)
(********************************************************************************)
(* A subst_t is a composition of parallel substitutions, expressed as a list of lists *)
let subst_to_string s = s |> List.map (fun (b, _) -> b.ppname.idText) |> String.concat ", "

//Lookup a bound var or a name in a parallel substitution
let subst_bv a s = Util.find_map s (function DB (i, t) when i=a.index -> Some t | _ -> None)
let subst_nm a s = Util.find_map s (function  
    | NM (x, i) when bv_eq a x -> Some (bv_to_tm ({x with index=i})) 
    | NT (x, t) when bv_eq a x -> Some t
    | _ -> None)
let subst_univ_bv x s = Util.find_map s (function 
    | UN(y, t) when x=y -> Some t
    | _ -> None)
let subst_univ_nm (x:univ_name) s = Util.find_map s (function 
    | UD(y, i) when x.idText=y.idText -> Some (U_bvar i)
    | _ -> None)

(* apply_until_some f s 
      applies f to each element of s until it returns (Some t)
*)
let rec apply_until_some f s = match s with
    | [] -> None
    | s0::rest ->
        match f s0 with
            | None -> apply_until_some f rest
            | Some st -> Some (rest, st)

let map_some_curry f x = function
    | None -> x
    | Some (a, b) -> f a b

let apply_until_some_then_map f s g t = 
    apply_until_some f s 
    |> map_some_curry g t

let rec subst_univ s u =
    let u = compress_univ u in
    match u with 
      | U_bvar x -> 
        apply_until_some_then_map (subst_univ_bv x) s subst_univ u

      | U_name  x ->
        apply_until_some_then_map (subst_univ_nm x) s subst_univ u

      | U_zero
      | U_unknown 
      | U_unif _ -> u
      | U_succ u -> U_succ (subst_univ s u)
      | U_max us -> U_max (List.map (subst_univ s) us)


let rec subst' (s:subst_t) t = match s with
  | [] 
  | [[]] -> t //force_uvar t
  | _ ->
    let t0 = force_delayed_thunk t in 
    match t0.n with
        | Tm_constant _      //a constant cannot be substituted
        | Tm_fvar _  -> t0   //fvar are never subject to substitution
        | Tm_uvar _ -> 
          let t0 = force_uvar t0 in
          begin match t0.n with
            | Tm_uvar _ -> t0            //unresolved uvar; nothing to substitute
            | Tm_name _ -> subst' s t0   //when a type is implicitly generalized, a uvar maybe resolved to a name
            | _ -> t0                    //otherwise, a uvar is always resolved to a closed term; so no substitution to do
          end

        | Tm_delayed(Inl(t', s'), m) ->
            //s' is the subsitution already associated with this node;
            //s is the new subsitution to add to it
            //compose substitutions by concatenating them
            //the order of concatenation is important!
          mk_Tm_delayed (Inl (t', s'@s)) t.pos

        | Tm_delayed(Inr _, _) -> 
          failwith "Impossible: force_delayed_thunk removes lazy delayed nodes"

        | Tm_bvar a ->
          apply_until_some_then_map (subst_bv a) s subst' t0

        | Tm_name a -> 
          apply_until_some_then_map (subst_nm a) s subst' t0

        | Tm_type u -> 
          mk (Tm_type (subst_univ s u)) None t0.pos 
          
        | _ -> mk_Tm_delayed (Inl(t0, s))  t.pos

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
      | GTotal t -> mk_GTotal (subst' s t)
      | Comp ct -> mk_Comp(subst_comp_typ' s ct)

and compose_subst (s1:subst_t) (s2:subst_t) = s1@s2

let shift n s = match s with 
    | DB(i, t) -> DB(i+n, t)
    | UN(i, t) -> UN(i+n, t)
    | NM(x, i) -> NM(x, i+n)
    | UD(x, i) -> UD(x, i+n)
    | NT _     -> s
let shift_subst n s = List.map (shift n) s
let shift_subst' n s = s |> List.map (shift_subst n)
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
        let p, m = aux n p in
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
        {pat with v=Pat_wild x}, n + 1 //these may be in scope in the inferred types of other terms, so shift the index

      | Pat_dot_term(x, t0) -> 
        let s = shift_subst' n s in
        let x = {x with sort=subst' s x.sort} in
        let t0 = subst' s t0 in 
        {pat with v=Pat_dot_term(x, t0)}, n //these are not in scope, so don't shift the index
  in aux 0 pat

let push_subst s t = 
    match t.n with 
        | Tm_delayed _ -> failwith "Impossible"

        | Tm_uvar _ 
        | Tm_constant _
        | Tm_fvar _
        | Tm_unknown -> t

        | Tm_type _
        | Tm_bvar _ 
        | Tm_name _  -> subst' s t

        | Tm_uinst(t', us) -> 
          //t' must be an fvar---it cannot be substituted
          //but the universes may be substituted
          let us = List.map (subst_univ s) us in
          mk_Tm_uinst t' us

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
          mk (Tm_meta(subst' s t0, Meta_pattern (ps |> List.map (subst_args' s)))) None t.pos

        | Tm_meta(t, m) -> 
          mk (Tm_meta(subst' s t,  m)) None t.pos 

let rec compress (t:term) = 
    let t = force_delayed_thunk t in
    match t.n with
        | Tm_delayed(Inl(t, s), memo) -> 
          let t' = compress (push_subst s t) in
          Unionfind.update_in_tx memo (Some t');
//          memo := Some t';
          t'
        | _ -> force_uvar t
            

let subst s t = subst' [s] t
let subst_comp s t = subst_comp' [s] t
let closing_subst bs = 
    List.fold_right (fun (x, _) (subst, n)  -> (NM(x, n)::subst, n+1)) bs ([], 0) |> fst 
let open_binders' bs = 
   let rec aux bs o = match bs with
        | [] -> [], o
        | (x, imp)::bs' -> 
          let x' = {freshen_bv x with sort=subst o x.sort} in
          let o = DB(0, bv_to_name x')::shift_subst 1 o in 
          let bs', o = aux bs' o in 
          (x',imp)::bs', o in
   aux bs [] 
let open_binders (bs:binders) = fst (open_binders' bs)
let open_term (bs:binders) t = 
   let bs', opening = open_binders' bs in
   bs', subst opening t
let open_comp (bs:binders) t = 
   let bs', opening = open_binders' bs in
   bs', subst_comp opening t
let open_pat (p:pat) : pat * subst = 
    let rec aux sub p = match p.v with 
       | Pat_disj [] -> failwith "Impossible: empty disjunction"
     
       | Pat_constant _ -> p, sub
       
       | Pat_disj(p::ps) -> 
         let p, sub = aux sub p in
         let ps = List.map (fun p -> fst (aux sub p)) ps in
         {p with v=Pat_disj(p::ps)}, sub

       | Pat_cons(fv, pats) ->
         let pats, sub = pats |> List.fold_left (fun (pats, sub) (p, imp) -> 
             let p, sub = aux sub p in
             ((p,imp)::pats, sub)) ([], sub) in
         {p with v=Pat_cons(fv, List.rev pats)}, sub

       | Pat_var x ->
         let x' = {freshen_bv x with sort=subst sub x.sort} in
         let sub = DB(0, bv_to_name x')::shift_subst 1 sub in 
         {p with v=Pat_var x'}, sub

       | Pat_wild x -> 
         let x' = {freshen_bv x with sort=subst sub x.sort} in
         let sub = DB(0, bv_to_name x')::shift_subst 1 sub in 
         {p with v=Pat_wild x'}, sub

       | Pat_dot_term(x, t0) -> 
         let x = {x with sort=subst sub x.sort} in
         let t0 = subst sub t0 in
         {p with v=Pat_dot_term(x, t0)}, sub in //these are not in scope, so don't shift the index
    
    aux [] p

let open_branch (p, wopt, e) = 
    let p, opening = open_pat p in
    let wopt = match wopt with 
        | None -> None
        | Some w -> Some (subst opening w) in
    let e = subst opening e in 
    (p, wopt, e)
    
let close (bs:binders) t = subst (closing_subst bs) t
let close_comp (bs:binders) (c:comp) = subst_comp (closing_subst bs) c
let close_binders (bs:binders) : binders =
    let rec aux s (bs:binders) = match bs with 
        | [] -> []
        | (x, imp)::tl ->  
          let x = {x with sort=subst s x.sort} in 
          let s' = NM(x, 0)::shift_subst 1 s in
          (x, imp)::aux s' tl in
    aux [] bs

let close_pat p = 
    let rec aux sub p = match p.v with
       | Pat_disj [] -> failwith "Impossible: empty disjunction"
     
       | Pat_constant _ -> p, sub
       
       | Pat_disj(p::ps) -> 
         let p, sub = aux sub p in
         let ps = List.map (fun p -> fst (aux sub p)) ps in
         {p with v=Pat_disj(p::ps)}, sub

       | Pat_cons(fv, pats) ->
         let pats, sub = pats |> List.fold_left (fun (pats, sub) (p, imp) -> 
             let p, sub = aux sub p in
             ((p,imp)::pats, sub)) ([], sub) in
         {p with v=Pat_cons(fv, List.rev pats)}, sub

       | Pat_var x ->
         let x = {x with sort=subst sub x.sort} in
         let sub = NM(x, 0)::shift_subst 1 sub in 
         {p with v=Pat_var x}, sub

       | Pat_wild x -> 
         let x = {x with sort=subst sub x.sort} in
         let sub = NM(x, 0)::shift_subst 1 sub in 
         {p with v=Pat_wild x}, sub

       | Pat_dot_term(x, t0) -> 
         let x = {x with sort=subst sub x.sort} in
         let t0 = subst sub t0 in
         {p with v=Pat_dot_term(x, t0)}, sub in //these are not in scope, so don't shift the index    
    aux [] p

let close_branch (p, wopt, e) = 
    let p, closing = close_pat p in 
    let wopt = match wopt with
        | None -> None
        | Some w -> Some (subst closing w) in
    let e = subst closing e in
    (p, wopt, e)

let univ_var_opening (us:univ_names) = 
    let n = List.length us - 1 in
    let s, us' = us |> List.mapi (fun i u -> 
        let u' = Syntax.new_univ_name (Some u.idRange) in
        UN(n - i, U_name u'), u') |> List.unzip in
    s, us'

let open_univ_vars  (us:univ_names) (t:term)  : univ_names * term = 
    let s, us' = univ_var_opening us in 
    let t = subst s t in
    us', t

let open_univ_vars_comp (us:univ_names) (c:comp) : univ_names * comp = 
    let s, us' = univ_var_opening us in 
    us', subst_comp s c

let close_univ_vars (us:univ_names) (t:term) : term = 
    let n = List.length us - 1 in
    let s = us |> List.mapi (fun i u -> UD(u, n - i)) in
    subst s t

let close_univ_vars_comp (us:univ_names) (c:comp) : comp = 
    let n = List.length us - 1 in
    let s = us |> List.mapi (fun i u -> UD(u, n - i)) in
    subst_comp s c

let is_top_level = function 
    | {lbname=Inr _}::_ -> true 
    | _ -> false

let open_let_rec lbs (t:term) =
    if is_top_level lbs then lbs, t //top-level let recs are not opened
    else failwith "NYI: open_let_rec"

let close_let_rec lbs (t:term) = 
    if is_top_level lbs then lbs, t //top-level let recs do not have to be closed
    else failwith "NYI: close_let_rec"

//requires: length bs = length args
let mk_subst_binders args = 
   let s, _ = List.fold_right (fun a (s, i) ->  DB(i, fst a)::s, i + 1) args ([], 0) in
   s

let subst_binders (bs:binders) (args:args) t = subst (mk_subst_binders args) t
let subst_binders_comp (bs:binders) (args:args) t = subst_comp (mk_subst_binders args) t
 

let close_tscheme (binders:binders) ((us, t) : tscheme) = 
    let n = List.length binders - 1 in
    let k = List.length us in 
    let s = List.mapi (fun i (x, _) -> NM(x, k + (n - i))) binders in
    let t = subst s t in 
    (us, t)

let close_univ_vars_tscheme (us:univ_names) ((us', t):tscheme) = 
   let n  = List.length us - 1 in
   let k = List.length us' in
   let s = List.mapi (fun i x -> UD(x, k + (n - i))) us in
   (us', subst s t)

let opening_of_binders (bs:binders) = 
  let n = List.length bs - 1 in
  bs |> List.mapi (fun i (x, _) -> DB(n - i, bv_to_name x))

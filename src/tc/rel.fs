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
module Microsoft.FStar.Tc.Rel

open Microsoft.FStar
open Microsoft.FStar.Options
open Microsoft.FStar.Tc
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Util
open Microsoft.FStar.Util
open Microsoft.FStar.Tc.Env
open Microsoft.FStar.Tc.Normalize
open Microsoft.FStar.Absyn.Syntax

let norm_targ env t = Tc.Normalize.norm_typ [Beta] env t
let whnf env t = Tc.Normalize.whnf env t |> Util.compress_typ
let sn env t = Tc.Normalize.norm_typ [Beta;Eta] env t |> Util.compress_typ
let sn_binders env binders = 
    binders |> List.map (function 
        | Inl a, imp -> 
          Inl ({a with sort=Tc.Normalize.norm_kind [Beta] env a.sort}), imp
        | Inr x, imp -> 
          Inr ({x with sort=norm_targ env x.sort}), imp)
let whnf_k env k = Tc.Normalize.norm_kind [Beta;Eta;WHNF] env k |> Util.compress_kind
let destruct_flex_t t = match t.n with
    | Typ_uvar(uv, k) -> (t, uv, k, [])
    | Typ_app({n=Typ_uvar(uv, k)}, args) -> (t, uv, k, args)
    | _ -> failwith "Not a flex-uvar"

(**********************************************************************************************************************)
(* Relations (equality and subsumption) between kinds, types, expressions and computations *)
(**********************************************************************************************************************)
type guard_t = 
  | Trivial
  | NonTrivial of formula

let rec is_trivial f : bool = 
    let bin_op f l = match l with 
        | [(Inl t1, _); (Inl t2, _)] -> f t1 t2
        | _ -> failwith "Impossible" in
    let connectives = [(Const.and_lid, bin_op (fun t1 t2 -> is_trivial t1 && is_trivial t2));
                       (Const.or_lid,  bin_op (fun t1 t2 -> is_trivial t1 || is_trivial t2));
                       (Const.imp_lid, bin_op (fun t1 t2 -> is_trivial t2));
                       (Const.true_lid, (fun _ -> true));
                       (Const.false_lid, (fun _ -> false));
                       ] in

    let fallback phi = match phi.n with 
        | Typ_lam(_, phi) -> is_trivial phi
        | _ -> false in

    match Util.destruct_typ_as_formula f with 
        | None -> fallback f
        | Some (BaseConn(op, arms)) -> 
           (match connectives |> List.tryFind (fun (l, _) -> lid_equals op l) with 
             | None -> false
             | Some (_, f) -> f arms)
        | Some (QAll(_, _, body)) 
        | Some (QEx(_, _, body)) -> is_trivial body
  
let simplify_guard (env:env) g =
  match g with 
    | Trivial -> g
    | NonTrivial f -> 
      //let f = Tc.Normalize.normalize env f in //NS: EXPENSIVE!
      if is_trivial f 
      then Trivial
      else NonTrivial f

let guard_to_string (env:env) = function  
  | Trivial -> "trivial"
  | NonTrivial f ->
      if debug env Medium then
        Normalize.formula_norm_to_string env f
      else
        "non-trivial"

let trivial t = match t with 
  | Trivial -> ()
  | NonTrivial _ -> failwith "impossible"

let conj_guard g1 g2 = match g1, g2 with 
  | Trivial, g
  | g, Trivial -> g
  | NonTrivial f1, NonTrivial f2 -> NonTrivial (Util.mk_conj f1 f2)

let rec close bs f = match bs with 
    | [] -> f
    | (Inl a, _)::rest -> 
      mk_Typ_app(Util.tforall_typ a.sort, [targ <| close rest f]) ktype f.pos
    | (Inr x, _)::rest -> 
      mk_Typ_app(Util.tforall, [targ <| close rest f]) ktype f.pos

let close_guard binders g = match g with 
    | Trivial -> g
    | NonTrivial f -> close binders 
                    (mk_Typ_lam(binders, f) (mk_Kind_arrow(binders, f.tk) f.pos) f.pos) |> NonTrivial
        
//////////////////////////////////////////////////////////////////////////
//Making substitutions for alpha-renaming 
//////////////////////////////////////////////////////////////////////////
let subst_binder b1 b2 s = 
    if is_null_binder b1 || is_null_binder b2 then s
    else match fst b1, fst b2 with 
        | Inl a, Inl b -> 
          if Util.bvar_eq a b 
          then s
          else Inl(b.v, btvar_to_typ a)::s
        | Inr x, Inr y -> 
          if Util.bvar_eq x y 
          then s
          else Inr(y.v, bvar_to_exp x)::s 
        | _ -> failwith "Impossible"


//////////////////////////////////////////////////////////////////////////
//Generating new unification variables/patterns
//////////////////////////////////////////////////////////////////////////
let new_kvar r binders =
  let wf k () = true in
  let u = Unionfind.fresh (Uvar wf) in
  mk_Kind_uvar (u, Util.args_of_non_null_binders binders) r, u

let new_tvar r binders k =
  let wf t tk = true in
  let binders = binders |> List.filter (fun x -> is_null_binder x |> not) in
  match binders with 
    | [] -> 
      let uv = Unionfind.fresh (Uvar wf) in 
      let uv = mk_Typ_uvar'(uv,k) k r in
      uv, uv
    | _ -> 
      let args = Util.args_of_non_null_binders binders in 
      let uv = Unionfind.fresh (Uvar wf) in 
      let k' = mk_Kind_arrow(binders, k) r in
      let uv = mk_Typ_uvar'(uv,k') k' r in
      mk_Typ_app(uv, args) k r, uv

let new_evar r binders t =
  let wf e t = true in 
  let binders = binders |> List.filter (fun x -> is_null_binder x |> not) in
  match binders with 
    | [] -> 
      let uv = Unionfind.fresh (Uvar wf) in 
      let uv = mk_Exp_uvar'(uv,t) t r in
      uv, uv
    | _ ->
      let args = Util.args_of_non_null_binders binders in 
      let uv = Unionfind.fresh (Uvar wf) in 
      let t' = mk_Typ_fun(binders, mk_Total t) ktype r in
      let uv = mk_Exp_uvar'(uv, t') t' r in
      match args with 
        | [] -> uv, uv
        | _ -> mk_Exp_app(uv, args) t r, uv

//////////////////////////////////////////////////////////////////////////
//Refinement subtyping with higher-order unification 
//with special treatment for higher-order patterns 
//////////////////////////////////////////////////////////////////////////
type rel = 
  | EQ 
  | SUB
let rel_to_string = function
  | EQ -> "="
  | SUB -> "<:"

type prob = 
  | KProb of bool * rel * knd * knd 
  | TProb of bool * rel * typ * typ
  | EProb of bool * rel * exp * exp 
  | CProb of bool * rel * comp * comp  //the bool in each case records whether or not it is a 'top-level' problem
let prob_to_string env = function 
  | KProb(_, rel, k1, k2) -> Util.format3 "\t%s\n\t\t%s\n\t%s" (Print.kind_to_string k1) (rel_to_string rel) (Print.kind_to_string k2)
  | TProb(_, rel, t1, t2) -> 
    Util.format "\t%s : %s (%s) \n\t\t%s\n\t%s : %s (%s)" 
        [//(Normalize.typ_norm_to_string env t1);
         Print.typ_to_string t1;
         Print.kind_to_string t1.tk;
         (Print.tag_of_typ t1) ;
         (rel_to_string rel);
         (Normalize.typ_norm_to_string env t2) ;
         (Print.kind_to_string t2.tk);
         (Print.tag_of_typ t2)]
  | EProb(_, rel, k1, k2) -> Util.format3 "\t%s \n\t\t%s\n\t%s" (Normalize.exp_norm_to_string env k1) (rel_to_string rel) (Normalize.exp_norm_to_string env k2)
  | CProb(_, rel, k1, k2) -> 
    Util.format3 "\t%s \n\t\t%s\n\t%s" (Normalize.comp_typ_norm_to_string env k1) (rel_to_string rel) (Normalize.comp_typ_norm_to_string env k2)
type uvar_inst =  //never a uvar in the co-domain of this map
  | UK of uvar_k * knd 
  | UT of (uvar_t * knd) * typ 
  | UE of (uvar_e * typ) * exp
  | UC of (uvar_t * knd) * typ
let str_uvi env ui =
  (* 
     CH: F* fails to type check this without the annotation on u.
     NS: Yes, this is by design. F* does not generalize inner lets by default. 
  *)
  let str (u:Unionfind.uvar<'a>) = if !Options.hide_uvar_nums then "?" else Unionfind.uvar_id u |> string_of_int in
  match ui with
  | UK (u, _) -> str u |> Util.format1 "UK %s"
  | UT ((u,_), t) -> str u |> (fun x -> Util.format2 "UT %s %s" x (Normalize.typ_norm_to_string env t))
  | UE ((u,_), _) -> str u |> Util.format1 "UE %s"
  | UC ((u,_), _) -> str u |> Util.format1 "UC %s"

let print_uvi env uvi = Util.fprint1 "%s\n" (str_uvi env uvi) 
    
type reason = string
type worklist = {
    attempting: list<prob>;
    deferred: list<(int * prob * reason)>;
    subst: list<uvar_inst>;
    top_t: option<typ>;      //the guard is either trivial; or a type of kind top_t => Type, where None => Type = Type and (Some t) => Type = t => Type
    guard: guard_t;
    ctr: int;
}
type solution = 
    | Success of list<uvar_inst> * guard_t
    | Failed of list<(int * prob * reason)>
let empty_worklist = {
    attempting=[];
    deferred=[];
    subst=[];
    top_t=None;
    guard=Trivial;
    ctr=0;
}
let singleton prob tk = {empty_worklist with attempting=[prob]; top_t=tk}

let reattempt (_, p, _) = p
let giveup env reason prob probs = 
    if debug env <| Options.Other "Rel"
    then Util.fprint2 "Failed %s:\n%s\n" reason (prob_to_string env prob);
    Failed <| (probs.ctr, prob, reason)::probs.deferred
let giveup_noex probs = Failed probs.deferred
let extend_subst ui wl = 
    //Util.print_string "Extending subst ... "; print_uvi ui;
   {wl with subst=ui::wl.subst; ctr=wl.ctr + 1}
let extend_subst' uis wl = 
   {wl with subst=uis@wl.subst; ctr=wl.ctr + 1}

let defer reason prob wl = {wl with deferred=(wl.ctr, prob, reason)::wl.deferred}
let attempt probs wl = {wl with attempting=probs@wl.attempting}

let close_predicate f = match (Util.compress_kind f.tk).n with 
    | Kind_arrow(bs, {n=Kind_type}) -> close bs f
    | Kind_type -> f
    | _ ->  failwith "Unexpected kind"

let close_guard_predicate = function
    | Trivial -> Trivial
    | NonTrivial f -> NonTrivial <| close_predicate f

let guard (env:env) top g probs =
    let mk_pred top_t f = match top_t with 
        | None -> f
        | Some t -> 
            let b = [null_v_binder t] in
            mk_Typ_lam(b, f) (mk_Kind_arrow(b, ktype) f.pos) f.pos in

    let g = simplify_guard env g in
    match g with 
    | Trivial -> probs
    | NonTrivial f -> 
        let g = if not top 
                then let qf = close_predicate f in 
                     match probs.top_t, probs.guard with 
                       | _, Trivial -> 
                         NonTrivial (mk_pred probs.top_t qf)
                       | Some _, NonTrivial {n=Typ_lam(bs, body); tk=tk; pos=p} -> 
                         NonTrivial (mk_Typ_lam(bs, Util.mk_conj body qf) tk p)
                       | None, NonTrivial g -> 
                         NonTrivial <| Util.mk_conj g qf
                       | _ -> failwith "Impossible"
                else match probs.top_t, probs.guard with 
                       | _, Trivial -> NonTrivial f
                       | None, NonTrivial g -> 
                         NonTrivial <| Util.mk_conj g f
                       | Some _, NonTrivial ({n=Typ_lam(xs, g)}) -> 
                            begin match f.n with 
                            | Typ_lam(ys, fbody) ->
                              let xs, args = Util.args_of_binders xs in
                              NonTrivial <| mk_Typ_lam(xs, Util.mk_conj g (Util.subst_typ (Util.subst_of_list ys args) fbody)) g.tk g.pos
                            | _ -> 
                              NonTrivial <| mk_Typ_lam(xs, Util.mk_conj g f) g.tk g.pos
                            end
                      | Some _, _ -> failwith "Impossible" in
        {probs with guard=g}

let commit env uvi = 
  let rec pre_kind_compat k1 k2 = 
   let k1, k2 = (compress_kind k1), (compress_kind k2) in
   match k1.n,k2.n with 
    | _, Kind_uvar uv 
    | Kind_uvar uv, _ -> true
    | Kind_type, Kind_type -> true
    | Kind_abbrev(_, k1), _ -> pre_kind_compat k1 k2
    | _, Kind_abbrev(_, k2) -> pre_kind_compat k1 k2
    | Kind_arrow(bs, k), Kind_arrow(bs', k') -> List.length bs = List.length bs' && pre_kind_compat k k'
    | _ -> Util.print_string (Util.format4 "(%s -- %s) Pre-kind-compat failed on %s and %s\n" (Range.string_of_range k1.pos) (Range.string_of_range k2.pos) (Print.kind_to_string k1) (Print.kind_to_string k2)); 
      false in

    uvi |> List.iter (fun uv -> 
        if debug env Extreme then (print_uvi env) uv;
        match uv with 
        | UK(u,k) -> Unionfind.change u (Fixed k)
        | UT((u,k),t) -> //ignore <| pre_kind_compat k t.tk; 
                         if debug env (Options.Other "Rel")
                         then Util.fprint2 "Commiting %s to %s\n" (Print.uvar_t_to_string (u,k)) (Print.typ_to_string t);
                         Unionfind.change u (Fixed t)
        | UE((u,_),e) -> Unionfind.change u (Fixed e)
        | UC((u,_),c) -> Unionfind.change u (Fixed c))
let find_uvar_k uv s = Util.find_map s (function UK(u, t) -> if Unionfind.equivalent uv u then Some t else None | _ -> None)
let find_uvar_t uv s = Util.find_map s (function UT((u,_), t) -> if Unionfind.equivalent uv u then Some t else None | _ -> None)
let find_uvar_e uv s = Util.find_map s (function UE((u,_), t) -> if Unionfind.equivalent uv u then Some t else None | _ -> None)
let find_uvar_c uv s = Util.find_map s (function UC((u,_), t) -> if Unionfind.equivalent uv u then Some t else None | _ -> None)

let intersect_vars v1 v2 = 
    let fvs1 = freevars_of_binders v1 in
    let fvs2 = freevars_of_binders v2 in 
    binders_of_freevars ({ftvs=Util.set_intersect fvs1.ftvs fvs2.ftvs; fxvs=Util.set_intersect fvs1.fxvs fvs2.fxvs})
type uvis = list<uvar_inst>
let rec compress_k (env:env) s k = 
    let k = Util.compress_kind k in 
    match k.n with 
        | Kind_uvar(uv, actuals) -> 
            (match find_uvar_k uv s with
                | None -> k
                | Some k' -> 
                    match k'.n with 
                        | Kind_lam(formals, body) -> 
                               let k = Util.subst_kind (Util.subst_of_list formals actuals) body in
                               compress_k env s k
                        | _ -> if List.length actuals = 0 
                               then compress_k env s k'
                               else failwith "Wrong arity for kind unifier")
        | _ -> k

let rec compress env s t =
    let t = Util.compress_typ t in
    match t.n with 
        | Typ_uvar (uv, _) ->
           (match find_uvar_t uv s with 
                | None -> whnf env t
                | Some t -> compress env s t)   
        | Typ_app({n=Typ_uvar(uv, k)}, args) -> 
            (match find_uvar_t uv s with 
                | Some t' -> 
                  let t' = compress env s t' in 
                  let t'' = mk_Typ_app(t', args) t.tk t.pos in 
                  let t''' = whnf env t'' in
                  if debug env Extreme then Util.fprint3 "Resolving uvar %s to\n\t%s\n\tnorm to %s\n" (Print.typ_to_string t) (Print.typ_to_string t'') (Print.typ_to_string t''');
                  t'''
                | _ -> whnf env t)
        | _ -> whnf env t

let rec compress_e (env:env) s e = 
    let e = Util.compress_exp e in
    match e.n with 
        | Exp_uvar (uv, t) -> 
           begin match find_uvar_e uv s with 
            | None -> e
            | Some e' -> compress_e env s e'
           end
        | Exp_app({n=Exp_uvar(uv, t)}, args) -> 
           begin match find_uvar_e uv s with 
            | None -> e
            | Some e' -> 
                let e' = compress_e env s e' in
                mk_Exp_app(e', args) e.tk e.pos //TODO: whnf for expressions?
           end
        | _ -> e

type match_result = 
  | MisMatch
  | HeadMatch
  | FullMatch

let head_match = function 
    | MisMatch -> MisMatch
    | _ -> HeadMatch

let rec head_matches env t1 t2 : match_result = 
  match (Util.compress_typ t1 |> Util.unascribe_typ).n, (Util.compress_typ t2 |> Util.unascribe_typ).n with 
    | Typ_btvar x, Typ_btvar y -> if Util.bvar_eq x y then FullMatch else MisMatch
    | Typ_const f, Typ_const g -> if Util.fvar_eq f g then FullMatch else MisMatch
    | Typ_btvar _, Typ_const _
    | Typ_const _, Typ_btvar _ -> MisMatch

    | Typ_refine(x, _), Typ_refine(y, _) -> head_matches env x.sort y.sort |> head_match
   
    | Typ_refine(x, _), _  -> head_matches env x.sort t2 |> head_match
    | _, Typ_refine(x, _)  -> head_matches env t1 x.sort |> head_match

    | Typ_fun _, Typ_fun _  -> HeadMatch
    
    | Typ_app(head, _), Typ_app(head', _) -> head_matches env head head'
    | Typ_app(head, _), _ -> head_matches env head t2
    | _, Typ_app(head, _) -> head_matches env t1 head
     
    | Typ_uvar (uv, _),  Typ_uvar (uv', _) -> if Unionfind.equivalent uv uv' then FullMatch else MisMatch

    | Typ_lam _, Typ_lam _ -> HeadMatch

    | _ -> MisMatch

let head_matches_delta env t1 t2 : (match_result * option<(typ*typ)>) =
    let success d r t1 t2 = (r, (if d then Some(t1, t2) else None)) in
    let fail () = (MisMatch, None) in
    let rec aux d t1 t2 = 
        match head_matches env t1 t2 with 
            | MisMatch -> 
                if d then fail() //already took a delta step
                else let t1 = Tc.Normalize.norm_typ [DeltaHard; Beta] env t1 in
                     let t2 = Tc.Normalize.norm_typ [DeltaHard; Beta] env t2 in
                     aux true t1 t2 
            | r -> success d r t1 t2 in
    aux false t1 t2

let binders_eq v1 v2 = 
  List.length v1 = List.length v2 
  && List.forall2 (fun ax1 ax2 -> match fst ax1, fst ax2 with 
        | Inl a, Inl b -> Util.bvar_eq a b
        | Inr x, Inr y -> Util.bvar_eq x y
        | _ -> false) v1 v2

let rec pat_vars env seen args : option<binders> = match args with 
    | [] -> Some (List.rev seen) 
    | (hd, imp)::rest -> 
        (match Util.unascribe_either hd with 
            | Inl t -> 
               let check_unique a = 
                    if seen |> Util.for_some (function 
                        | Inl b, _ -> bvd_eq a.v b.v
                        | _ -> false)
                    then None //not a pattern
                    else pat_vars env ((Inl a, imp)::seen) rest in
               begin match t.n with 
                | Typ_btvar a -> check_unique a
                | _ -> (match (norm_targ env t).n with
                            | Typ_btvar a -> check_unique a
                            | _ -> None)
               end
            | Inr {n=Exp_bvar x} ->
                if seen |> Util.for_some (function 
                    | Inr y, _ -> bvd_eq x.v y.v
                    | _ -> false)
                then None //not a pattern
                else pat_vars env ((Inr x, imp)::seen) rest
            | te -> None) //not a pattern

let decompose_binder (bs:binders) ktec_v (rebuild_base:binders -> ktec -> 'a) : ((list<ktec> -> 'a) * list<(binders * ktec)>) = 
    let fail () = failwith "Bad reconstruction" in
    let rebuild ktecs = 
        let rec aux new_bs bs ktecs = match bs, ktecs with 
            | [], [ktec] -> rebuild_base (List.rev new_bs) ktec
            | (Inl a, imp)::rest, K k::rest' -> aux ((Inl ({a with sort=k}), imp)::new_bs) rest rest'
            | (Inr x, imp)::rest, T t::rest' -> aux ((Inr ({x with sort=t}), imp)::new_bs) rest rest'
            | _ -> fail () in
        aux [] bs ktecs in
          
    let rec mk_b_ktecs (binders, b_ktecs) = function 
        | [] -> List.rev ((binders, ktec_v)::b_ktecs)
        | hd::rest ->
            let b_ktec = match fst hd with 
                | Inl a -> (binders, K a.sort)
                | Inr x -> (binders, T x.sort) in
            let binders' = if is_null_binder hd then binders else binders@[hd] in
            mk_b_ktecs (binders', b_ktec::b_ktecs) rest in

    rebuild, mk_b_ktecs ([], []) bs
 
let rec decompose_kind (env:env) k : (list<ktec> -> knd) * list<(binders * ktec)> = 
    let fail () = failwith "Bad reconstruction" in
    let k0 = k in
    let k = Util.compress_kind k in 
    match k.n with
        | Kind_type 
        | Kind_effect -> 
            let rebuild = function 
                | [] -> k
                | _ -> fail () in 
            rebuild, []

        | Kind_arrow(bs, k) -> 
          decompose_binder bs (K k) (fun bs -> function 
            | K k -> mk_Kind_arrow(bs, k) k0.pos
            | _ -> fail ())

        | Kind_abbrev(_, k) -> 
          decompose_kind env k
        
        | _ -> failwith "Impossible"

let rec decompose_typ env t : (list<ktec> -> typ) * (typ -> bool) * list<(binders * ktec)> =
    let t = Util.compress_typ t in
    match t.n with 
        | Typ_app(hd, args) ->
          let rebuild args' = 
            let args = List.map2 (fun x y -> match x, y with
                | (Inl _, imp), T t -> Inl t, imp
                | (Inr _, imp), E e -> Inr e, imp
                | _ -> failwith "Bad reconstruction") args args' in
            mk_Typ_app(hd, args) t.tk t.pos in
          let b_ktecs = args |> List.map (function (Inl t, _) -> [], T t | (Inr e, _) -> [], E e) in
          let matches t' =
            let hd', _ = Util.head_and_args t' in
            head_matches env hd hd' <> MisMatch in
          rebuild, matches, b_ktecs

        | Typ_ascribed(t, _) -> 
          decompose_typ env t
        
        | Typ_fun(bs, c) -> 
          if debug env Extreme then Util.fprint1 "Decomposing function with effect %s" (comp_to_comp_typ c |> (fun c -> Print.sli c.effect_name));
          let rebuild, b_ktecs = 
              decompose_binder bs (C c) (fun bs -> function 
                | C c -> mk_Typ_fun(bs, c) ktype t.pos
                | _ -> failwith "Bad reconstruction") in
          let matches t = match (Util.compress_typ t).n with 
            | Typ_fun _ -> true
            | _ -> false in
          rebuild, matches, b_ktecs

        | Typ_refine(x, phi) -> 
          let rebuild, b_ktecs = 
              decompose_binder [v_binder x] (T phi) (fun bs tt -> match bs, tt with 
                | [(Inr y, _)], T phi' -> mk_Typ_refine(y, phi') ktype t.pos
                | _ -> failwith "Bad reconstruction") in
          let matches t = match (Util.compress_typ t).n with 
            | Typ_refine _ -> true
            | _ -> false in
          rebuild, matches, b_ktecs
        

        | _ -> 
          let rebuild = function
            | [] -> t
            | _ -> failwith "Bad reconstruction" in
          rebuild, (fun t -> true), []

type flex_t = (typ * uvar_t * knd * args)
type im_or_proj_t = ((uvar_t * knd) * list<arg> * binders * ((list<ktec> -> typ) * (typ -> bool) * list<(binders * ktec)>))
type im_or_proj_k = (uvar_k * list<arg> * binders * ((list<ktec> -> knd) *  list<(binders * ktec)>))

let occurs_check env uk t = 
    let uvs = Util.uvars_in_typ t in 
    let occurs_ok = not (Util.set_mem uk uvs.uvars_t) in
    let msg = 
        if occurs_ok then None
        else Some (Util.format4 "occurs-check failed (%s occurs in {%s} uvars of %s normalized to %s)" 
                        (Print.uvar_t_to_string uk) 
                        (Util.set_elements uvs.uvars_t |> List.map Print.uvar_t_to_string |> String.concat ", ")
                        (Print.typ_to_string t)
                        (Normalize.typ_norm_to_string env t)) in
    occurs_ok, msg

let occurs_check_e env ut e = 
    let uvs = Util.uvars_in_exp e in 
    let occurs_ok = not (Util.set_mem ut uvs.uvars_e) in
    let msg = 
        if occurs_ok then None
        else Some (Util.format3 "occurs-check failed (%s occurs in {%s} uvars of %s normalized to %s)" 
                        (Print.uvar_e_to_string ut) 
                        (Util.set_elements uvs.uvars_e |> List.map Print.uvar_e_to_string |> String.concat ", ")
                        (Print.exp_to_string e)) in
    occurs_ok, msg

let rec solve (env:Tc.Env.env) (probs:worklist) : solution = 
//    printfn "Solving TODO:\n%s;;" (List.map prob_to_string probs.attempting |> String.concat "\n\t");
    match probs.attempting with 
       | hd::tl -> 
        let probs = {probs with attempting=tl} in
         (match hd with 
            | KProb (top, rel, k1, k2) -> solve_k top env rel k1 k2 probs
            | TProb (top, rel, t1, t2) -> solve_t top env rel t1 t2 probs
            | EProb (top, rel, e1, e2) -> solve_e top env rel e1 e2 probs
            | CProb (top, rel, c1, c2) -> solve_c top env rel c1 c2 probs)
       | [] ->
         match probs.deferred with 
            | [] -> Success (probs.subst, probs.guard) //Yay ... done!
            | _ -> 
              let ctr = List.length probs.subst in 
              let attempt, rest = probs.deferred |> List.partition (fun (c, t, _) -> c < ctr) in
              match attempt with 
                 | [] -> Failed probs.deferred //no progress made to help with solving deferred problems; fail
                 | _ -> solve env ({probs with attempting=attempt |> List.map reattempt; deferred=rest})

and imitate (env:Tc.Env.env) (probs:worklist) (p:im_or_proj_t) : solution =
    let ((u,k), ps, xs, (h, _, qs)) = p in
    let xs = sn_binders env xs in
//U p1..pn =?= h q1..qm
//if h is not a free variable
//extend_subst: (U -> \x1..xn. h (G1(x1..xn), ..., Gm(x1..xm)))
//sub-problems: Gi(p1..pn) =?= qi
    let r = Env.get_range env in
    let gs_xs, sub_probs = qs |> List.map (function 
        | binders, K ki -> 
            let gi_xs, gi = new_kvar r (xs@binders) in
            let gi_ps = mk_Kind_uvar(gi, ps@Util.args_of_non_null_binders binders) r in //xs are all non-null
            K gi_xs, [KProb(false, EQ, gi_ps, ki)]

        | binders, T ti -> 
            let gi_xs, gi = new_tvar r (xs@binders) ti.tk in
            let gi_ps = match ps@Util.args_of_non_null_binders binders with 
                | [] -> gi
                | args -> mk_Typ_app(gi, args) ti.tk ti.pos in
            T gi_xs, [TProb(false, EQ, gi_ps, ti)]
        
        | binders, C ci -> 
            let vars = xs@binders in
            let im_t t =                 
                let s, u = new_tvar t.pos vars t.tk in 
                s, (t, u) in
            let im_e e = 
                let f, u = new_evar e.pos vars e.tk in
                f, (e,u) in

            let gi_xs, im = match ci.n with 
                    | Total t -> 
                        let s, (t, u) = im_t t in
                        let im : Syntax.args -> list<prob> = fun ps -> [TProb(false, EQ, t, mk_Typ_app'(u, ps) t.tk t.pos)] in
                        mk_Total s, im
                        
                    | Comp c -> 
                        let sres, im_res = im_t c.result_typ in
                        let args, ims = c.effect_args |> List.map (fun (a, imp) -> match a with 
                            | Inl t ->  
                                let s, im_t = im_t t in
                                (Inl s, imp), Inl im_t
                            | Inr e -> 
                                let f, im_e = im_e e in
                                (Inr f, imp), Inr im_e) |> List.unzip in
                        let im : Syntax.args -> list<prob> = fun ps -> (Inl im_res)::ims |> List.map (function 
                                | Inl(t, u) -> TProb(false, EQ, t, mk_Typ_app'(u, ps) t.tk t.pos)
                                | Inr(e, u) -> EProb(false, EQ, e, mk_Exp_app'(u, ps) e.tk e.pos)) in
                        if debug env High then Util.fprint1 "Imitating computation %s" (Print.sli c.effect_name);
                        let gi_xs = mk_Comp <| {
                            effect_name=c.effect_name;
                            result_typ=sres;
                            effect_args=args;
                            flags=c.flags
                        }  in 
                        gi_xs, im in
            C gi_xs, im (ps@Util.args_of_non_null_binders binders)

        | _, E ei -> 
            let gi_xs, gi = new_evar r xs ei.tk in
            let gi_ps = match ps with 
                | [] -> gi
                | _ -> mk_Exp_app(gi, ps) ei.tk r in
            E gi_xs, [EProb(false, EQ, gi_ps, ei)]) |> List.unzip in

    let im = match xs with 
        | [] -> h gs_xs
        | _ -> mk_Typ_lam(xs, h gs_xs) k r in
    if Tc.Env.debug env <| Options.Other "Rel" 
    then Util.fprint3 "Imitating %s (%s)\nsub_probs = %s\n" (Print.typ_to_string im) (Print.tag_of_typ im) (List.map (prob_to_string env) (List.flatten sub_probs) |> String.concat ", ");
    let probs = extend_subst (UT((u,k), im)) probs in
    solve env (attempt (List.flatten sub_probs) probs)

and imitate_k (top:bool) (env:Tc.Env.env) (probs:worklist) (p:im_or_proj_k) : solution = 
    let (u, ps, xs, (h, qs)) = p in
//U p1..pn =?= h q1..qm
//extend_subst: (U -> \x1..xn. h (G1(x1..xn), ..., Gm(x1..xm)))
//sub-problems: Gi(p1..pn) =?= qi
    let r = Env.get_range env in 
    let gs_xs, sub_probs = qs |> List.map (function 
        | _, C _ 
        | _, E _ -> failwith "Impossible"

        | binders, K ki -> 
          let gi_xs, gi = new_kvar r (xs@binders) in
          let gi_ps = mk_Kind_uvar(gi, (ps@Util.args_of_non_null_binders binders)) r in
          K gi_xs, KProb(false, EQ, gi_ps, ki)

        | _, T ti ->  //TODO: why ignore binders here?
          let gi_xs, gi = new_tvar r xs ti.tk in
          let gi_ps = mk_Typ_app(gi, ps) ti.tk r in
          T gi_xs, TProb(false, EQ, gi_ps, ti)) |> List.unzip in

    let im = mk_Kind_lam(xs, h gs_xs) r in
    let probs = extend_subst (UK(u, im)) probs in 
    solve env (attempt sub_probs probs)

and project (env:Tc.Env.env) (probs:worklist) (i:int) (p:im_or_proj_t) : solution = 
    let (u, ps, xs, (h, matches, qs)) = p in
//U p1..pn =?= h q1..qm
//extend subst: U -> \x1..xn. xi(G1(x1...xn) ... Gk(x1..xm)) ... where k is the arity of ti
//sub-problems: pi(G1(p1..pn)..Gk(p1..pn)) =?= h q1..qm
    let r = Env.get_range env in
    let pi = List.nth ps i in
    let rec gs k = 
        let bs, k = Util.kind_formals k in
        let rec aux subst bs = match bs with 
            | [] -> [], [] //gs (Util.subst_kind subst k)
            | hd::tl -> 
                let gi_xs, gi_ps, subst = match fst hd with 
                    | Inl a -> 
                        let k_a = Util.subst_kind subst a.sort in
                        let gi_xs, gi = new_tvar r xs k_a in
                        let gi_xs = Tc.Normalize.eta_expand env gi_xs in
                        let gi_ps = mk_Typ_app(gi, ps) k_a r in
                        let subst = if is_null_binder hd then subst else Inl(a.v, gi_xs)::subst in
                        targ gi_xs, targ gi_ps, subst

                    | Inr x ->  
                        let t_x = Util.subst_typ subst x.sort in 
                        let gi_xs, gi = new_evar r xs t_x in
                        let gi_xs = Tc.Normalize.eta_expand_exp env gi_xs in
                        let gi_ps = mk_Exp_app(gi, ps) t_x r in
                        let subst = if is_null_binder hd then subst else Inr(x.v, gi_xs)::subst in
                        varg gi_xs, varg gi_ps, subst in
                let gi_xs', gi_ps' = aux subst tl in
                gi_xs::gi_xs', gi_ps::gi_ps' in
          aux [] bs in

    match fst pi, fst <| List.nth xs i with 
        | Inl pi, Inl xi -> 
            if not <| matches pi then giveup_noex probs
            else let g_xs, g_ps = gs xi.sort in 
                 let xi = btvar_to_typ xi in
                 let proj = mk_Typ_lam(xs, mk_Typ_app'(xi, g_xs) ktype r) (snd u) r in
                 let sub = TProb(false, EQ, mk_Typ_app'(proj, ps) ktype r, h <| List.map snd qs) in
                 if debug env <| Options.Other "Rel" then Util.fprint2 "Projecting %s\n\tsubprob=%s\n" (Print.typ_to_string proj) (prob_to_string env sub);
                 let probs = extend_subst (UT(u, proj)) probs in
                 solve env ({probs with attempting=sub::probs.attempting})
        | _ -> giveup_noex probs

and solve_k (top:bool) (env:Env.env) (rel:rel) (k1:knd) (k2:knd) (probs:worklist) : solution = 
    if Util.physical_equality k1 k2 then solve env probs else
    let k1 = compress_k env probs.subst k1 in 
    let k2 = compress_k env probs.subst k2 in 
    if Util.physical_equality k1 k2 then solve env probs else
    let r = Env.get_range env in 

    match k1.n, k2.n with 
     | Kind_type, Kind_type 
     | Kind_effect, Kind_effect -> solve env probs

     | Kind_abbrev(_, k1), _ -> solve_k top env rel k1 k2 probs
     | _, Kind_abbrev(_, k2) -> solve_k top env rel k1 k2 probs

     | Kind_arrow(bs1, k1'), Kind_arrow(bs2, k2') -> 
       solve_binders env bs1 bs2 rel (KProb(top, rel, k1, k2)) probs
       (fun subst subprobs -> solve env (attempt (KProb(false, rel, k1', Util.subst_kind subst k2')::subprobs) probs)) 
       
     | Kind_uvar(u1, args1), Kind_uvar (u2, args2) -> //flex-flex ... unify, if patterns
       let maybe_vars1 = pat_vars env [] args1 in
       let maybe_vars2 = pat_vars env [] args2 in
       begin match maybe_vars1, maybe_vars2 with 
            | None, _
            | _, None -> giveup env "flex-flex: non patterns" (KProb(top, rel, k1, k2)) probs
            | Some xs, Some ys -> 
              if Unionfind.equivalent u1 u2 && binders_eq xs ys
              then solve env probs
              else
                    //U1 xs =?= U2 ys
                    //zs = xs intersect ys, U fresh
                    //U1 = \xs. U zs
                    //U2 = \ys. U zs
                  let zs = intersect_vars xs ys in
                  let u, _ = new_kvar r zs in 
                  let k1 = mk_Kind_lam(xs, u) r in
                  let k2 = mk_Kind_lam(ys, u) r in
                  let probs = extend_subst (UK(u1, k1)) probs |> extend_subst (UK(u2, k2)) in
                  solve env probs
       end

     | Kind_uvar(u, args), _ -> //flex-rigid: only resolve kind variables to closed kind-lambdas
       let maybe_vars1 = pat_vars env [] args in
       begin match maybe_vars1 with 
         | Some xs -> 
           let fvs1 = freevars_of_binders xs in
           let fvs2 = Util.freevars_kind k2 in
           let uvs2 = Util.uvars_in_kind k2 in
           if Util.set_is_subset_of fvs2.ftvs fvs1.ftvs
              && Util.set_is_subset_of fvs2.fxvs fvs1.fxvs
              && not(Util.set_mem u uvs2.uvars_k)
           then let k1 = mk_Kind_lam(xs, k2) r in //Solve in one-step
                solve env (extend_subst (UK(u, k1)) probs)
           else (if debug env High then Util.print_string "Imitating kind ... ";
                 imitate_k top env probs (u, xs |> Util.args_of_non_null_binders, xs, decompose_kind env k2) )
        | None -> 
           giveup env (Util.format1 "flex-rigid: not a pattern (args=%s)" (Print.args_to_string args)) (KProb(top, rel, k1, k2)) probs
       end
          
     | _, Kind_uvar _ -> //rigid-flex ... re-orient
       solve_k top env EQ k2 k1 probs

     | Kind_delayed _, _ 
     | Kind_unknown, _
     | _, Kind_delayed _ 
     | _, Kind_unknown -> failwith "Impossible"

     | _ -> giveup env "head mismatch (k-1)" (KProb(top, rel, k1, k2)) probs

and solve_binders (env:Tc.Env.env) (bs1:binders) (bs2:binders) (rel:rel) (orig:prob) (probs:worklist) 
                  (rhs:list<subst_elt> -> list<prob> -> solution) : solution =
   let rec aux subprobs subst bs1 bs2 = match bs1, bs2 with 
        | [], [] -> rhs subst subprobs
        | hd1::tl1, hd2::tl2 -> 
            begin match fst hd1, fst hd2 with 
                | Inl a, Inl b -> aux (KProb(false, rel, Util.subst_kind subst b.sort, a.sort)::subprobs) (subst_binder hd1 hd2 subst) tl1 tl2 
                | Inr x, Inr y -> aux (TProb(false, rel, Util.subst_typ subst y.sort, x.sort)::subprobs) (subst_binder hd1 hd2 subst) tl1 tl2
                | _ -> giveup env "arrow mismatch" orig probs
            end
        | _ -> giveup env "arrow arity" orig probs in
       aux [] [] bs1 bs2

and solve_t_flex_flex (top:bool) (env:Tc.Env.env) (orig:prob) 
                      (lhs:flex_t) (rhs:flex_t) (probs:worklist) : solution = 
    let (t1, u1, k1, args1) = lhs in
    let (t2, u2, k2, args2) = rhs in 
    let maybe_pat_vars1 = pat_vars env [] args1 in
    let maybe_pat_vars2 = pat_vars env [] args2 in
    let r = t2.pos in
    let warn s1 s2 = 
        if Tc.Env.debug env <| Options.Other "Rel"
        then Util.fprint6 "Breaking generality in flex/flex case solving %s = %s by setting lhs=%s :: %s and rhs=%s :: %s\n" 
            (Normalize.typ_norm_to_string env t1) (Normalize.typ_norm_to_string env t2)
            (Normalize.typ_norm_to_string env s1) (Print.kind_to_string s1.tk)
            (Normalize.typ_norm_to_string env s2) (Print.kind_to_string s2.tk) in
                  
    let solve_neither_pat () = 
        let u, _ = new_tvar (Env.get_range env) [] ktype in 
        let sol = if Unionfind.equivalent u1 u2
                  then let rec aux sub args1 args2 = match args1, args2 with  
                        | [], [] -> solve env ({probs with attempting=sub; deferred=[]; top_t=None; guard=Trivial; ctr=0})
                        | (Inl t1, _)::rest1, (Inl t2, _)::rest2 -> aux (TProb(false, EQ, t1, t2)::sub) rest1 rest2 
                        | (Inr e1, _)::rest1, (Inr e2, _)::rest2 -> aux (EProb(false, EQ, e1, e2)::sub) rest1 rest2 
                        | _ -> solve env (defer "flex/flex unequal arity" orig probs) in //defer  ...can this ever be solved?
                       begin match aux [] args1 args2 with
                                | Failed _ 
                                | Success (_, NonTrivial _) -> 
                                    let t1 = Util.close_for_kind u k1 in
                                    warn t1 t2; [UT((u1, k1), t1)]
                                | Success (sol, _) -> sol 
                       end
                  else  (* neither side is an applicable pattern; Instead of giving up, revert to solving with a simple type (breaking generality) *)
                       let t1 = Util.close_for_kind u k1 in
                       let t2 = Util.close_for_kind u k2 in
                       let _ = warn t1 t2 in
                       [UT((u1, k1), t1); 
                        UT((u2, k2), t2)] in
        let probs = extend_subst' sol probs in
        solve env probs in

    let solve_one_pat (t1, u1, k1, xs) (t2, u2, k2, args2) = 
        if Tc.Env.debug env <| Options.Other "Rel"
        then Util.fprint2 "Trying flex-flex one pattern (%s) with %s\n" (Print.typ_to_string t1) (Print.typ_to_string t2);
        let t2 = sn env t2 in
        let rhs_vars = Util.freevars_typ t2 in
        let occurs_ok, _ = occurs_check env (u1,k1) t2 in
        if not occurs_ok
        then (if Tc.Env.debug env <| Options.Other "Rel"
              then Util.print_string "Occurs check failed... breaking generality\n";
              solve_neither_pat()) //occurs check failed; default by breaking generality
        else let lhs_vars = freevars_of_binders xs in
             if Util.fvs_included rhs_vars lhs_vars
             then (* solve by instantiating u1 to imitate t2 *)
                  let sol = [UT((u1, k1), mk_Typ_lam(xs, t2) k1 t1.pos)] in
                  let probs = extend_subst' sol probs in
                  solve env probs
             else let zs, _ = Util.kind_formals k2 in
                  if List.length zs <> List.length args2
                  then (if Tc.Env.debug env <| Options.Other "Rel"
                        then Util.print_string "Arity check failed on RHS: kind uOccurs check failed... breaking generality\n";
                        solve_neither_pat()) //unexpected arity; default by breaking generality
                  else  
                      //U1 x1..xn =?= U2 t1..tm
                      //ys = {xi} intersect FV(t1..tm)
                      //U1 -> \x1..xn. U y1..yk
                      //U2 -> \z1...zm. U (G1 z1..zm) ... (Gk z1..zm)
                      //Gi(t1..tm) =?= yi
                      let ys = binders_of_freevars ({ftvs=Util.set_intersect rhs_vars.ftvs lhs_vars.ftvs; 
                                                     fxvs=Util.set_intersect rhs_vars.fxvs lhs_vars.fxvs}) in
                      let u_yi, u = new_tvar t1.pos ys ktype in
                      let u1_inst = UT((u1, k1), mk_Typ_lam(xs, u_yi) k1 t1.pos) in
                      let r = t2.pos in
                      let gi_zi, sub_probs = List.map (fun yi -> match fst yi with 
                        | Inl ai -> 
                            let gi_zs, gi = new_tvar r zs ai.sort in
                            let gi_ps = mk_Typ_app(gi, args2) ai.sort r in
                            targ gi_zs, TProb(false, EQ, gi_ps, Util.btvar_to_typ ai)

                        | Inr xi -> 
                            let gi_zs, gi = new_evar r zs xi.sort in
                            let gi_ps = mk_Exp_app(gi, args2) xi.sort r in
                            varg gi_zs, EProb(false, EQ, gi_ps, Util.bvar_to_exp xi)) ys |> List.unzip in
                      let u2_inst = UT((u2,k2), mk_Typ_lam(zs, mk_Typ_app(u, gi_zi) ktype r) k2 r) in
                      let sol = [u1_inst; u2_inst] in
                      let _ = if Tc.Env.debug env <| Options.Other "Rel"
                              then Util.fprint2 "Flex-Flex: double imitation\n\tsols = %s\nsubprobs=\n%s\n" 
                                                (List.map (str_uvi env) sol |> String.concat "\n\t") 
                                                (List.map (prob_to_string env) sub_probs |> String.concat "\n") in
                      solve env (attempt sub_probs (extend_subst' sol probs)) in
             
        
//    if Unionfind.equivalent u1 u2
//    then let rec aux sub args1 args2 = match args1, args2 with  
//            | [], [] -> solve env (attempt sub probs)
//            | (Inl t1, _)::rest1, (Inl t2, _)::rest2 -> aux (TProb(false, EQ, t1, t2)::sub) rest1 rest2 
//            | (Inr e1, _)::rest1, (Inr e2, _)::rest2 -> aux (EProb(false, EQ, e1, e2)::sub) rest1 rest2 
//            | _ -> solve env (defer "flex/flex unequal arity" orig probs) in //defer  ...can this ever be solved?
//         aux [] args1 args2 
//    else 
    begin match maybe_pat_vars1, maybe_pat_vars2 with 
        | None, None -> solve_neither_pat () //neither is a pattern; break generality

        | Some xs, None -> 
            solve_one_pat (t1, u1, k1, xs) rhs

        | None, Some ys -> 
            solve_one_pat (t2, u2, k2, ys) lhs

        | Some xs, Some ys -> 
            let extend_and_solve sols probs = 
                if debug env High then Util.fprint1 "Flex-flex: %s" (sols |> List.map (str_uvi env) |> String.concat ", ");
                let probs = extend_subst' sols probs in
                solve env probs in
                     
            if (Unionfind.equivalent u1 u2 && binders_eq xs ys)
            then begin 
                 if Tc.Env.debug env <| Options.Other "Rel"
                 then Util.fprint1 "Solved %s ... identity\n" (prob_to_string env orig);
                 solve env probs
            end
            else //U1 xs =?= U2 ys
                 //zs = xs intersect ys, U fresh
                 //U1 = \x1 x2. U zs
                 //U2 = \y1 y2 y3. U zs
                let xs = sn_binders env xs in
                let ys = sn_binders env ys in
                let zs = intersect_vars xs ys in
                let u_zs, _ = new_tvar r zs t2.tk in
                let sub1 = match xs with 
                    | [] -> u_zs 
                    | _ -> mk_Typ_lam(xs, u_zs) k1 r in
                let sub1 = norm_targ env sub1 in
                let occurs_ok, msg = occurs_check env (u1,k1) sub1 in
                if not occurs_ok
                then giveup env (Option.get msg) orig probs
                else let sol1 = [UT((u1, k1), sub1)] in
                     if Unionfind.equivalent u1 u2
                     then extend_and_solve sol1 probs
                     else let sub2 = match ys with 
                            | [] -> u_zs
                            | _ -> mk_Typ_lam(ys, u_zs) k2 r in
                          let sub2 = norm_targ env sub2 in
                          let occurs_ok, msg = occurs_check env (u2,k2) sub2 in
                          if not occurs_ok 
                          then giveup env (Option.get msg) orig probs
                          else let sol = sol1@[UT((u2,k2), sub2)] in
                               extend_and_solve sol probs
    end

and solve_t_flex_rigid (top:bool) (env:Tc.Env.env) (orig:prob) (lhs:flex_t) (t2:typ) (probs:worklist) = 
    let (t1, uv, k, args_lhs) = lhs in
    let maybe_pat_vars = pat_vars env [] args_lhs in
    let subterms ps = 
        let xs = Util.kind_formals k |> fst in
        let xs = Util.name_binders xs in
        (uv,k), ps, xs, decompose_typ env t2 in

    let rec imitate_or_project n st i = 
        if i >= n then giveup env "flex-rigid case failed all backtracking attempts" orig probs
        else if i = -1 
        then match imitate env probs st with
                | Failed _ -> imitate_or_project n st (i + 1) //backtracking point
                | sol -> sol
        else match project env probs i st with
                | Failed _ -> imitate_or_project n st (i + 1) //backtracking point
                | sol -> sol in

    let check_head fvs1 t2 =
        let hd, _ = Util.head_and_args t2 in 
        match hd.n with 
            | Typ_fun _
            | Typ_refine _ 
            | Typ_const _
            | Typ_lam _  -> true
            | _ ->             
                let fvs_hd = Util.freevars_typ hd in
                if Util.fvs_included fvs_hd fvs1
                then true
                else (Util.fprint1 "Free variables are %s" (Print.freevars_to_string fvs_hd); false) in
            
    let imitate_ok t2 = (* -1 means begin by imitating *)
        let fvs_hd = Util.head_and_args t2 |> fst |> Util.freevars_typ in
        if Util.set_is_empty fvs_hd.ftvs
        then -1 (* yes, start by imitating *)
        else 0 (* no, start by projecting *) in

   match maybe_pat_vars with 
     | Some vars -> 
            let t1 = sn env t1 in
            let t2 = sn env t2 in 
            let fvs1 = Util.freevars_typ t1 in
            let fvs2 = Util.freevars_typ t2 in
            let occurs_ok, msg = occurs_check env (uv,k) t2 in
            if not occurs_ok 
            then giveup env (Option.get msg) orig probs
            else if Util.fvs_included fvs2 fvs1
            then //fast solution for flex-pattern/rigid case
                let _  = if debug env <| Options.Other "Rel" 
                         then Util.fprint3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" (Print.typ_to_string t1) (Print.freevars_to_string fvs1) (Print.freevars_to_string fvs2) in
                let sol = match vars with 
                | [] -> t2
                | _ -> mk_Typ_lam(sn_binders env vars, t2) k t1.pos in
                //let _ = if debug env then printfn "Fast solution for %s \t -> \t %s" (Print.typ_to_string t1) (Print.typ_to_string sol) in
                solve env (extend_subst (UT((uv,k), sol)) probs)
            else if check_head fvs1 t2 
            then (let im_ok = -1 in //imitate_ok t2 in
                  if debug env <| Options.Other "Rel" 
                  then Util.fprint4 "Pattern %s with fvars=%s failed fvar check: %s ... %s\n" 
                            (Print.typ_to_string t1) (Print.freevars_to_string fvs1) 
                            (Print.freevars_to_string fvs2) (if im_ok < 0 then "imitating" else "projecting");
                  imitate_or_project (List.length args_lhs) (subterms args_lhs) im_ok)
            else giveup env "fre-variable check failed on a non-redex" orig probs
    | None ->   
            if check_head (Util.freevars_typ t1) t2
            then (let im_ok = imitate_ok t2 in
                  if debug env <| Options.Other "Rel" 
                  then Util.fprint2 "Not a pattern (%s) ... %s\n" (Print.typ_to_string t1) (if im_ok < 0 then "imitating" else "projecting");
                  imitate_or_project (List.length args_lhs) (subterms args_lhs) im_ok)
            else giveup env "head-symbol is free" orig probs
   
  
and solve_t (top:bool) (env:Env.env) (rel:rel) (t1:typ) (t2:typ) (probs:worklist) : solution = 
    if Util.physical_equality t1 t2 then solve env probs else
    let t1 = compress env probs.subst t1 in
    let t2 = compress env probs.subst t2 in 
    if Util.physical_equality t1 t2 then solve env probs else
    let _ = if debug env (Options.Other "Rel") then Util.fprint2 "Attempting (top level? %s):\n%s\n" (if top then "true" else "false") (prob_to_string env (TProb(top, rel, t1, t2))) in
//    printfn "Tag t1 = %s, t2 = %s" (Print.tag_of_typ t1) (Print.tag_of_typ t2);
    if Util.physical_equality t1 t2 then solve env probs else
    let r = Env.get_range env in
    let solve_and_close env binders subprobs probs p = 
        let sol = match p with 
            | TProb(top, rel, t1, t2) -> solve_t top env rel t1 t2 empty_worklist 
            | CProb(top, rel, c1, c2) -> solve_c top env rel c1 c2 empty_worklist
            | _ -> failwith "impos" in
        begin match sol with 
            | Success (subst, guard_f) -> 
                let probs = extend_subst' subst probs |> guard env false (close_guard binders guard_f) in
                solve env (attempt subprobs probs)

            | Failed reasons -> 
                giveup env (reasons |> List.map (fun (_, _, r) -> r) |> String.concat ", ")  p probs
        end in 

    match t1.n, t2.n with
      | Typ_ascribed(t, _), _
      | Typ_meta(Meta_pattern(t, _)), _ 
      | Typ_meta(Meta_labeled(t, _, _)), _
      | Typ_meta(Meta_refresh_label(t, _, _)), _
      | Typ_meta(Meta_named(t, _)), _ -> solve_t top env rel t t2 probs

      | _, Typ_ascribed(t, _)
      | _, Typ_meta(Meta_pattern(t, _))
      | _, Typ_meta(Meta_labeled(t, _, _))
      | _, Typ_meta(Meta_refresh_label(t, _, _))
      | _, Typ_meta(Meta_named(t, _)) -> solve_t top env rel t1 t probs

      | Typ_btvar a, Typ_btvar b -> 
        if Util.bvd_eq a.v b.v 
        then solve env probs
        else giveup env "unequal type variables" (TProb(top, rel, t1, t2)) probs (* TODO: They may be equal by refinement, though *)

      | Typ_fun(bs1, c1), Typ_fun(bs2, c2) ->
        let curry_fun n bs c = 
         let bs, rest = Util.first_N n bs in
         (bs, mk_Total(mk_Typ_fun(rest, c) ktype c.pos)) in
            
        let (bs1, c1), (bs2, c2) = 
            let l1 = List.length bs1 in
            let l2 = List.length bs2 in
            if l1 = l2
            then (bs1, c1), (bs2, c2)
            else if l1 > l2
            then curry_fun l2 bs1 c1, (bs2, c2) 
            else (bs1, c1), curry_fun l1 bs2 c2 in
        solve_binders env bs1 bs2 rel (TProb(top, rel, t1, t2)) probs
        (fun subst subprobs -> 
            let c2 = Util.subst_comp subst c2 in
            let rel = if !Options.verify then EQ else rel in
            solve_and_close env bs1 subprobs probs (CProb(false, rel, c1, c2)))

      | Typ_lam(bs1, t1'), Typ_lam(bs2, t2') -> 
        solve_binders env bs1 bs2 rel (TProb(top, rel, t1, t2)) probs
        (fun subst subprobs -> 
            let prob = TProb(false, rel, t1', Util.subst_typ subst t2') in
            if Env.debug env <| Options.Other "Rel"
            then (Util.fprint3 "Kind of lhs is %s body type %s is %s\n" (Normalize.kind_norm_to_string env t1.tk) (Normalize.typ_norm_to_string env t1') (Normalize.kind_norm_to_string env t1'.tk);
                  Util.fprint1 "Sub-problems from Typ_lam:\n%s\n" ((prob::subprobs) |> List.map (prob_to_string env) |> String.concat "\n"));
            solve_and_close env bs1 subprobs probs prob)

      | Typ_refine(x1, phi1), Typ_refine(x2, phi2) -> 
        let base_prob = TProb(top, rel, x1.sort, x2.sort) in
        let subst = [Inr(x2.v, Util.bvar_to_exp x1)] in
        let phi2 = Util.subst_typ subst phi2 in
        begin match rel with 
            | EQ -> 
              solve_and_close env [v_binder x1] [base_prob] probs (TProb(false, EQ, phi1, phi2))
               
            | SUB -> 
              let g = NonTrivial <| mk_Typ_lam([v_binder x1], Util.mk_imp phi1 phi2) (mk_Kind_arrow([v_binder x1], ktype) r) r in
              let probs = guard env top g probs in
              solve env (attempt [base_prob] probs)
        end

      (* flex-flex *)
      | Typ_uvar _, Typ_uvar _
      | Typ_app({n=Typ_uvar _}, _), Typ_uvar _ 
      | Typ_uvar _, Typ_app({n=Typ_uvar _}, _)
      | Typ_app({n=Typ_uvar _}, _), Typ_app({n=Typ_uvar _}, _) -> 
        solve_t_flex_flex top env (TProb(top, rel, t1, t2)) (destruct_flex_t t1) (destruct_flex_t t2) probs
   
      (* flex-rigid *)
      | Typ_uvar _, _
      | Typ_app({n=Typ_uvar _}, _), _ -> 
        solve_t_flex_rigid top env (TProb(top, rel, t1, t2)) (destruct_flex_t t1) t2 probs

      (* rigid-flex ... reorient *)
      | _, Typ_uvar _ 
      | _, Typ_app({n=Typ_uvar _}, _) ->
        solve_t top env EQ t2 t1 probs 

      | Typ_refine(x, phi1), _ ->
        if rel=EQ
        then giveup env "refinement subtyping is not applicable" (TProb(top, rel, t1, t2)) probs //but t2 may be able to take delta steps
        else solve_t top env rel x.sort t2 probs

      | _, Typ_refine(x, phi2) -> 
        if rel=EQ
        then giveup env "refinement subtyping is not applicable" (TProb(top, rel, t1, t2)) probs //but t1 may be able to take delta steps
        else let g = NonTrivial <| mk_Typ_lam([v_binder (bvd_to_bvar_s x.v t1)], phi2) (mk_Kind_arrow([null_v_binder t1], ktype) r) r in
             solve_t top env rel t1 x.sort (guard env top g probs)   
      
      | Typ_btvar _, _
      | Typ_const _, _
      | Typ_app _, _
      | _, Typ_btvar _
      | _, Typ_const _ 
      | _, Typ_app _ -> 
         let m, o = head_matches_delta env t1 t2 in
         begin match m, o  with 
            | (MisMatch, _) -> 
                giveup env "head mismatch (t-1)" (TProb(top, rel, t1, t2)) probs        //heads definitely do not match

            | (_, Some (t1, t2)) ->
               //              printfn "Head match with delta %s, %s" (Print.typ_to_string head) (Print.typ_to_string head');
               probs |> solve_t top env rel t1 t2

            | (_, None) -> //head matches head'
                if debug env <| Options.Other "Rel" then Util.fprint2 "Head matches: %s and %s\n" (Print.typ_to_string t1) (Print.typ_to_string t2);
                let head, args = Util.head_and_args t1 in
                let head', args' = Util.head_and_args t2 in
                if List.length args = List.length args'
                then let subprobs = List.map2 (fun a a' -> match fst a, fst a' with 
                    | Inl t, Inl t' -> TProb(false, EQ, t, t')
                    | Inr v, Inr v' -> EProb(false, EQ, v, v')
                    | _ -> failwith "Impossible" (*terms are well-kinded*)) args args' in
                    let subprobs = match m with 
                        | FullMatch -> subprobs
                        | _ -> TProb(false, EQ, head, head')::subprobs in
                    solve env (attempt subprobs probs)
                else giveup env (Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" 
                            (Print.typ_to_string head)
                            (Print.args_to_string args)
                            (Print.typ_to_string head')
                            (Print.args_to_string args')) 
                            (TProb(top, rel, t1, t2)) probs
          end

      | _ -> giveup env (Util.format2 "head mismatch (t-2): %s and %s" (Print.tag_of_typ t1) (Print.tag_of_typ t2)) (TProb(top, rel, t1, t2)) probs

and solve_c (top:bool) (env:Env.env) (rel:rel) (c1:comp) (c2:comp) (probs:worklist) : solution =
    if Util.physical_equality c1 c2 then solve env probs
    else let _ = if debug env <| Options.Other "Rel" then Util.fprint2 "solve_c %s and %s\n" (Print.comp_typ_to_string c1) (Print.comp_typ_to_string c2) in
         let r = Env.get_range env in
         let c1_0, c2_0 = c1, c2 in
         match c1.n, c2.n with
               | Total t1, Total t2 -> //rigid-rigid 1
                 solve_t false env rel t1 t2 probs
               
               | Total _,  Comp _ -> solve_c top env rel (mk_Comp <| comp_to_comp_typ c1) c2 probs
               | Comp _, Total _ -> solve_c top env rel c1 (mk_Comp <| comp_to_comp_typ c2) probs
               
               | Comp _, Comp _ ->
                 if (Util.is_ml_comp c1 && Util.is_ml_comp c2) 
                    || (Util.is_total_comp c1 && (Util.is_total_comp c2 || Util.is_ml_comp c2))
                 then solve_t false env rel (Util.comp_result c1) (Util.comp_result c2) probs 
                 else
                     let c1_comp = Util.comp_to_comp_typ c1 in
                     let c2_comp = Util.comp_to_comp_typ c2 in
                     if rel=EQ && lid_equals c1_comp.effect_name c2_comp.effect_name
                     then let sub_probs = List.map2 (fun arg1 arg2 -> match fst arg1, fst arg2 with 
                            | Inl t1, Inl t2 -> TProb(false, EQ, t1, t2)
                            | Inr e1, Inr e2 -> EProb(false, EQ, e1, e2)
                            | _ -> failwith "impossible") c1_comp.effect_args c2_comp.effect_args in
                          solve env (attempt sub_probs probs)
                     else
                         let c1 = Normalize.weak_norm_comp env c1 in
                         let c2 = Normalize.weak_norm_comp env c2 in
                         if debug env <| Options.Other "Rel" then Util.fprint2 "solve_c for %s and %s\n" (c1.effect_name.str) (c2.effect_name.str);
                         begin match Tc.Env.monad_leq env c1.effect_name c2.effect_name with
                           | None -> giveup env "incompatible monad ordering" (CProb(top, rel, c1_0, c2_0)) probs
                           | Some edge ->
                             let is_null_wp_2 = c2.flags |> Util.for_some (function TOTAL | MLEFFECT | SOMETRIVIAL -> true | _ -> false) in
                             let wpc1, wpc2 = match c1.effect_args, c2.effect_args with 
                               | (Inl wp1, _)::_, (Inl wp2, _)::_ -> wp1, wp2 
                               | _ -> failwith (Util.format2 "Got effects %s and %s, expected normalized effects" (Print.sli c1.effect_name) (Print.sli c2.effect_name)) in
                             let res_t_prob = TProb(false, rel, c1.result_typ, c2.result_typ) in
                             if Util.physical_equality wpc1 wpc2 
                             then solve env (attempt [res_t_prob] probs)
                             else let c2_decl : monad_decl = Tc.Env.get_monad_decl env c2.effect_name in
                                  let g = 
                                    if is_null_wp_2 
                                    then let _ = if debug env <| Options.Other "Rel" then Util.print_string "Using trivial wp ... \n" in
                                         NonTrivial <| mk_Typ_app(c2_decl.trivial, [targ c1.result_typ; targ <| edge.mlift c1.result_typ wpc1]) ktype r 
                                    else let wp2_imp_wp1 = mk_Typ_app(c2_decl.wp_binop, 
                                                                      [targ c2.result_typ; 
                                                                       targ wpc2; 
                                                                       targ <| Util.ftv Const.imp_lid (Const.kbin ktype ktype ktype); 
                                                                       targ <| edge.mlift c1.result_typ wpc1]) wpc2.tk r in
                                         NonTrivial <| mk_Typ_app(c2_decl.wp_as_type, [targ c2.result_typ; targ wp2_imp_wp1]) ktype r  in
                                  let probs = guard env top g probs in 
                                  solve env (attempt [res_t_prob] probs)
                         end

                                
and solve_e (top:bool) (env:Env.env) (rel:rel) (e1:exp) (e2:exp) (probs:worklist) : solution = 
    let e1 = compress_e env probs.subst e1 in 
    let e2 = compress_e env probs.subst e2 in
    let _ = if debug env <| Options.Other "Rel" then Util.fprint1 "Attempting:\n%s\n" (prob_to_string env (EProb(top, rel, e1, e2))) in
  
    let solve_flex_rigid (u1, t1) r1 args1 e2 = 
        let maybe_vars1 = pat_vars env [] args1 in
        let sub_problems xs args =
            let gi_xi, gi_pi = args |> List.map (function 
            | Inl t, imp -> 
                let gi_xi, gi = new_tvar t.pos xs t.tk in
                let gi_pi = mk_Typ_app(gi, args1) t.tk t.pos in
                (Inl gi_xi, imp), TProb(false, EQ, gi_pi, t)
            | Inr v, imp ->
                let gi_xi, gi = new_evar v.pos xs v.tk in 
                let gi_pi = mk_Exp_app(gi, args1) v.tk v.pos in
                (Inr gi_xi, imp), EProb(false, EQ, gi_pi, v)) |> List.unzip in
          gi_xi, gi_pi in
         
        let project_e head2 args2 = 
            //u p1..pn =?= y a1 .. am
            //if pi = y  
            //u = \x1..xn. xi (G1 (x1..xn), ..., Gm (x1..xn))
            //Gi(p1..pn) =?= ai 
            let giveup reason = giveup env (Util.format1 "flex-rigid: refusing to project expressions (%s)" reason) (EProb(top, rel, e1, e2)) probs in
            match (Util.compress_exp head2).n with 
                | Exp_bvar y -> 
                    let all_xs, tres = match Util.function_formals t1 with
                        | None -> [], t1
                        | Some (xs, c) -> xs, Util.comp_result c in
                    if List.length all_xs <> List.length args1
                    then giveup (Util.format2 "unequal arity:\n\texpetced binders %s\n\tgot args {%s}" (Print.binders_to_string ", " all_xs) (Print.args_to_string args2))
                    else let rec aux xs args = match xs, args with 
                            | [], [] -> giveup "variable to project not found"
                            | [], _
                            | _, [] -> failwith "impossible"
                            | (Inl _, _)::xs, (Inl _, _)::args -> aux xs args
                            | (Inr xi, _)::xs, (Inr arg, _)::args -> 
                                begin match (Util.compress_exp arg).n with 
                                       | Exp_bvar z -> 
                                          if Util.bvar_eq y z (* found the variable to project *)
                                          then let gi_xi, gi_pi = sub_problems all_xs args2 in
                                               let sol = mk_Exp_abs(all_xs, mk_Exp_app'(Util.bvar_to_exp xi, gi_xi) tres e1.pos) t1 e1.pos in
                                               if Tc.Env.debug env <| Options.Other "Rel"
                                               then Util.fprint3 "Projected: %s -> %s\nSubprobs=\n%s\n" (Print.uvar_e_to_string (u1,t1)) (Print.exp_to_string sol) (gi_pi |> List.map (prob_to_string env) |> String.concat "\n");
                                               solve env (attempt gi_pi (extend_subst (UE((u1, t1), sol)) probs))
                                          else aux xs args
                                       | _ -> aux xs args
                                end
                            | x::xs, arg::args -> giveup (Util.format2 "type incorrect term---impossible: expected %s; got %s\n" (Print.binder_to_string x) (Print.arg_to_string arg)) in
                          aux all_xs args1
                | _ -> giveup "rhs head term is not a variable" in

        let imitate_e () = 
            //u1 p1..pn =?= h a1..am
            //if h not occurs in u1 and h not free
            //u1 = \x1..xn. h (G1(x1...xn), ..., Gm(x1..xn))
            //and Gi(p1..pn) =?= ai
            if Tc.Env.debug env <| Options.Other "Rel"
            then Util.fprint2 "Imitating expressions: %s =?= %s\n" (Print.exp_to_string e1) (Print.exp_to_string e2);
            let head2, args2 = Util.head_and_args_e e2 in
            let fvhead = Util.freevars_exp head2 in
            let occurs_ok, _ = occurs_check_e env (u1, t1) head2 in
            if Util.fvs_included fvhead Syntax.no_fvs && occurs_ok
            then let xs, tres = match Util.function_formals t1 with
                        | None -> [], t1
                        | Some (xs, c) -> xs, Util.comp_result c in
                 let gi_xi, gi_pi = sub_problems xs args2 in
                 let sol = mk_Exp_abs(xs, mk_Exp_app(head2, gi_xi) tres e1.pos) t1 e1.pos in
                 if Tc.Env.debug env <| Options.Other "Rel"
                 then Util.fprint3 "Imitated: %s -> %s\nSubprobs=\n%s\n" (Print.uvar_e_to_string (u1,t1)) (Print.exp_to_string sol) (gi_pi |> List.map (prob_to_string env) |> String.concat "\n");
                 solve env (attempt gi_pi (extend_subst (UE((u1, t1), sol)) probs))
            else if occurs_ok 
            then project_e head2 args2
            else giveup env "flex-rigid: occurs check failed" (EProb(top, rel, e1, e2)) probs in
      

        begin match maybe_vars1 with 
        | None -> imitate_e ()
        | Some xs -> 
            let fvs1 = freevars_of_binders xs in 
            let fvs2 = Util.freevars_exp e2 in 
            let occurs_ok, _ = occurs_check_e env (u1, t1) e2 in
            if Util.set_is_subset_of fvs2.ftvs fvs1.ftvs 
                && Util.set_is_subset_of fvs2.fxvs fvs1.fxvs 
                && occurs_ok
            then // U1 xs =?= e2
                // U1 = \xs. e2
                let sol = mk_Exp_abs(xs, e2) t1 r1 in
                solve env (extend_subst (UE((u1,t1), sol)) probs)
            else imitate_e ()
        end in

    let solve_flex_flex (u1, t1) r1 args1 (u2, t2) r2 args2 = //flex-flex: solve only patterns
      let maybe_vars1 = pat_vars env [] args1 in
      let maybe_vars2 = pat_vars env [] args2 in
      begin match maybe_vars1, maybe_vars2 with 
        | None, _
        | _, None -> solve env (defer "flex/flex not a pattern" (EProb(top, rel, e1, e2)) probs) //refuse to solve non-patterns
        | Some xs, Some ys -> 
          if (Unionfind.equivalent u1 u2 && binders_eq xs ys)
          then solve env probs
          else 
              //U1 xs =?= U2 ys
              //zs = xs intersect ys, U fresh
              //U1 = \x1 x2. U zs
              //U2 = \y1 y2 y3. U zs 
              let zs = intersect_vars xs ys in 
              let u, _ = new_evar (Env.get_range env) zs e2.tk in
              let sub1 = mk_Exp_abs(xs, u) t1 r1 in
              let sub2 = mk_Exp_abs(ys, u) t2 r2 in
              solve env (extend_subst (UE((u1,t1), sub1)) probs |> extend_subst (UE((u2,t2), sub2))) 
      end in

    match e1.n, e2.n with 
    | Exp_bvar x1, Exp_bvar x1' -> 
      if Util.bvd_eq x1.v x1'.v
      then solve env probs
      else solve env (guard env top (NonTrivial <| Util.mk_eq e1 e2) probs)

    | Exp_fvar (fv1, _), Exp_fvar (fv1', _) -> 
      if lid_equals fv1.v fv1'.v
      then solve env probs
      else giveup env "free-variables unequal" (EProb(top, rel, e1, e2)) probs //distinct top-level free vars are never provably equal

    | Exp_constant s1, Exp_constant s1' -> 
      let const_eq s1 s2 = match s1, s2 with 
          | Const_bytearray(b1, _), Const_bytearray(b2, _) -> b1=b2
          | Const_string(b1, _), Const_string(b2, _) -> b1=b2
          | _ -> s1=s2 in
      if const_eq s1 s1'
      then solve env probs
      else giveup env "constants unequal" (EProb(top, rel, e1, e2)) probs

    | Exp_ascribed(e1, _), _ -> 
      solve_e top env rel e1 e2 probs

    | _, Exp_ascribed(e2, _) -> 
      solve_e top env rel e1 e2 probs

    | Exp_uvar(u1, t1), Exp_uvar(u2, t2) -> 
      solve_flex_flex (u1, t1) e1.pos [] (u2, t2) e2.pos []
    | Exp_app({n=Exp_uvar(u1,t1); pos=r1}, args1), Exp_uvar(u2, t2) -> 
      solve_flex_flex (u1, t1) r1 args1 (u2, t2) e2.pos []
    | Exp_uvar(u1, t1), Exp_app({n=Exp_uvar(u2, t2); pos=r2}, args2) -> 
      solve_flex_flex (u1, t1) e1.pos [] (u2, t2) e2.pos args2
    | Exp_app({n=Exp_uvar(u1,t1); pos=r1}, args1), Exp_app({n=Exp_uvar(u2, t2); pos=r2}, args2) -> 
      solve_flex_flex (u1, t1) r1 args1 (u2, t2) r2 args2

    | Exp_uvar(u1, t1), _ ->
      solve_flex_rigid (u1, t1) e1.pos [] e2
    | Exp_app({n=Exp_uvar(u1,t1); pos=r1}, args1), _ -> //flex-rigid
      solve_flex_rigid (u1, t1) r1 args1 e2 

    | _, Exp_uvar _ 
    | _, Exp_app({n=Exp_uvar _}, _) -> //rigid-flex ... reorient
     solve_e top env EQ e2 e1 probs

    | _ -> //TODO: check that they at least have the same head? 
     solve env (guard env top (NonTrivial <| Util.mk_eq e1 e2) probs)  
          
let explain env d = 
    if debug env <| Options.Other "ExplainRel"
    then  d |> List.iter (fun (_, p, reason) -> 
                    Util.fprint2 "Problem:\n%s\nFailed because: %s\n" (prob_to_string env p) reason)

let solve_and_commit env top_t prob err = 
  let sol = solve env (singleton prob top_t) in
  match sol with 
    | Success (s, guard) -> 
      //printfn "Successs ... got guard %s\n" (guard_to_string env guard);
      commit env s; Some guard
    | Failed d -> 
        explain env d;
        err d

let try_keq env k1 k2 : option<guard_t> = 
  let prob = KProb(true, EQ, norm_kind [Beta] env k1, norm_kind [Beta] env k2) in
  solve_and_commit env None prob (fun _ -> None)

let keq env t k1 k2 : guard_t = 
  match try_keq env k1 k2 with 
    | None -> 
      let r = match t with 
        | None -> Tc.Env.get_range env
        | Some t -> t.pos in
      begin match t with 
        | None -> raise (Error(Tc.Errors.incompatible_kinds env k2 k1, r))
        | Some t -> raise (Error(Tc.Errors.expected_typ_of_kind env k2 t k1, r))
      end
    | Some g -> g

let try_teq env t1 t2 : option<guard_t> = 
 if debug env <| Other "Rel" then Util.fprint2 "teq of %s and %s\n" (Print.typ_to_string t1) (Print.typ_to_string t2);
 let prob = TProb(true, EQ, t1, t2) in //norm_typ [Beta; Eta] env t1, norm_typ [Beta; Eta] env t2) in
 let g = solve_and_commit env (Some t1) prob (fun _ -> None) in
 let g = match g with 
    | None -> None
    | Some g -> Some (close_guard_predicate g) in
 g
    
let teq env t1 t2 : guard_t = 
 match try_teq env t1 t2 with
    | None -> raise (Error(Tc.Errors.basic_type_error env None t2 t1, Tc.Env.get_range env))
    | Some g ->
      if debug env <| Other "Rel" then Util.fprint3 "teq of %s and %s succeeded with guard %s\n" (Print.typ_to_string t1) (Print.typ_to_string t2) (guard_to_string env g);
      g

let subkind env k1 k2 : guard_t = 
 if debug env <| Other "Rel" 
   || debug env Options.High 
 then Util.fprint2 "try_subkind of %s and %s\n" (Print.kind_to_string k1) (Print.kind_to_string k2);
 let prob  = KProb(true, SUB, whnf_k env k1, whnf_k env k2) in
 Util.must <| solve_and_commit env None prob (fun _ -> 
    raise (Error(Tc.Errors.incompatible_kinds env k1 k2, Tc.Env.get_range env)))

let try_subtype env t1 t2 = 
 if debug env <| Other "Rel" then Util.fprint2 "try_subtype of %s and %s\n" (Normalize.typ_norm_to_string env t1) (Normalize.typ_norm_to_string env t2);
 let g = solve_and_commit env (Some t1) (TProb(true, SUB, t1, t2))
 (fun _ -> None) in
 if debug env <| Options.Other "Rel" 
    && Util.is_some g
 then Util.fprint3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" (Normalize.typ_norm_to_string env t1) (Normalize.typ_norm_to_string env t2) (guard_to_string env (Util.must g));
 g

let subtype_fail env t1 t2 = 
    raise (Error(Tc.Errors.basic_type_error env None t2 t1, Tc.Env.get_range env))

let subtype env t1 t2 : guard_t = 
  if debug env Low then Util.fprint1 "(%s) Subtype test \n" (Range.string_of_range <| Env.get_range env);
  match try_subtype env t1 t2 with
    | Some f -> f
    | None -> subtype_fail env t1 t2

let trivial_subtype env eopt t1 t2 = 
 if debug env <| Other "Rel" then Util.fprint2 "try_subtype of %s and %s\n" (Print.typ_to_string t1) (Print.typ_to_string t2);
 let err () =
    let r = Tc.Env.get_range env in
    raise (Error(Tc.Errors.basic_type_error env eopt t2 t1, r)) in
 let sol = solve env (singleton (TProb(true, SUB, t1, t2)) (Some t1)) in
 match sol with 
    | Success (s, Trivial) -> commit env s 
    | Success _ -> err()
    | Failed d -> explain env d; err()
        
let sub_comp env c1 c2 = 
  if debug env <| Other "Rel" then Util.fprint2 "sub_comp of %s and %s\n" (Print.comp_typ_to_string c1) (Print.comp_typ_to_string c2);
  let gopt = solve_and_commit env None (CProb(true, SUB, c1, c2))
     (fun _ -> None) in
 if debug env <| Options.Other "Rel" 
    && Util.is_some gopt
 then Util.fprint3 "sub_compe succeeded: %s <: %s\n\tguard is %s\n" (Print.comp_typ_to_string c1) (Print.comp_typ_to_string c2) (guard_to_string env (Util.must gopt));
 gopt


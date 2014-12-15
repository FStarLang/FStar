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
//////////////////////////////////////////////////////////////////////////
//Refinement subtyping with higher-order unification 
//with special treatment for higher-order patterns 
//////////////////////////////////////////////////////////////////////////

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



//////////////////////////////////////////////////////////////////////////
//Making substitutions for alpha-renaming 
//////////////////////////////////////////////////////////////////////////
let mk_subst_binder b1 b2 s = 
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


(* --------------------------------------------------------- *)
(* <new_uvar> Generating new unification variables/patterns  *)
(* --------------------------------------------------------- *)
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

(* --------------------------------------------------------- *)
(* </new_uvar>                                               *)
(* --------------------------------------------------------- *)

(* --------------------------------------------------------- *)
(* <type defs> The main types of the constraint solver       *)
(* --------------------------------------------------------- *)
type rel = 
  | EQ 
  | SUB
  | SUBINV  (* sub-typing/sub-kinding, inverted *)

type problem<'a,'b> = {               //Try to prove: lhs rel rhs ~> guard        
    lhs:'a;
    relation:rel;   
    rhs:'a;
    element:option<'b>;               //where, guard is a predicate on this term (which appears free in/is a subterm of the guard) 
    closing_context:binders;          //and must be closed by this context
    reason: list<string>;             //why we generated this problem, for error reporting
    loc: Range.range;                 //and the source location where this arose
}

type prob = 
  | KProb of problem<knd,typ>
  | TProb of problem<typ,exp>
  | EProb of problem<exp,unit>
  | CProb of problem<comp,unit>

type probs = list<prob>

type guard_formula = 
  | Trivial
  | NonTrivial of formula

type guard_t = {
  guard_f: guard_formula;
  carry:   probs;
  slack:   list<typ>;
}

(* Instantiation of unification variables *)
type uvi =  
  | UK of uvar_k * knd 
  | UT of (uvar_t * knd) * typ 
  | UE of (uvar_e * typ) * exp
  | UC of (uvar_t * knd) * typ

(* The set of problems currently being addressed *)
type worklist = {
    attempting: probs;
    deferred:   list<(int * prob)>;  //flex-flex cases, non patterns, and subtyping constraints involving a unification variable, 
    subst:      list<uvi>;           //the partial solution derived so far
    guard:      guard_formula;       //the logical condition gathered so far
    ctr:        int;                 //a counter incremented each time we extend subst, used to detect if we've made progress
    slack_vars: list<typ>;           //all the slack variables introduced so far
    defer_ok:   bool;                //whether or not carrying constraints is ok---at the top-level, this flag is false
}

type solution = 
    | Success of list<uvi> * guard_t
    | Failed  of prob * string
(* --------------------------------------------------------- *)
(* </type defs>                                              *)
(* --------------------------------------------------------- *)

(* ------------------------------------------------*)
(* <Printing> (mainly for debugging) *)
(* ------------------------------------------------*)
let rel_to_string = function
  | EQ -> "="
  | SUB -> "<:"
  | SUBINV -> ":>"


let prob_to_string env = function 
  | KProb p -> Util.format3 "\t%s\n\t\t%s\n\t%s" (Print.kind_to_string p.lhs) (rel_to_string p.relation) (Print.kind_to_string p.rhs)
  | TProb p -> 
    Util.format "\t%s (%s) \n\t\t%s\n\t%s (%s)" 
        [(Normalize.typ_norm_to_string env p.lhs);
         (Print.tag_of_typ p.lhs) ;
         (rel_to_string p.relation);
         (Normalize.typ_norm_to_string env p.rhs);
         (Print.tag_of_typ p.rhs)]
  | EProb p -> Util.format3 "\t%s \n\t\t%s\n\t%s" (Normalize.exp_norm_to_string env p.lhs) (rel_to_string p.relation) (Normalize.exp_norm_to_string env p.rhs)
  | CProb p -> Util.format3 "\t%s \n\t\t%s\n\t%s" (Normalize.comp_typ_norm_to_string env p.lhs) (rel_to_string p.relation) (Normalize.comp_typ_norm_to_string env p.rhs)

let guard_to_string (env:env) g = 
  let form = match g.guard_f with 
      | Trivial -> "trivial"
      | NonTrivial f ->
          if debug env <| Options.Other "Rel" 
          then Normalize.formula_norm_to_string env f
          else "non-trivial" in
  let carry = List.map (prob_to_string env) g.carry |> String.concat ", " in
  Util.format2 "{guard_f=%s;\ndeferred=%s;}\n" form carry

let uvi_to_string env uvi = 
  (* By design. F* does not generalize inner lets by default. *)
  let str (u:Unionfind.uvar<'a>) = if !Options.hide_uvar_nums then "?" else Unionfind.uvar_id u |> string_of_int in
  match uvi with
      | UK (u, _) -> str u |> Util.format1 "UK %s"
      | UT ((u,_), t) -> str u |> (fun x -> Util.format2 "UT %s %s" x (Normalize.typ_norm_to_string env t))
      | UE ((u,_), _) -> str u |> Util.format1 "UE %s"
      | UC ((u,_), _) -> str u |> Util.format1 "UC %s"
(* ------------------------------------------------*)
(* </Printing> *)
(* ------------------------------------------------*)

(* ------------------------------------------------*)
(* <guard_formula ops> Operations on guard_formula *)
(* ------------------------------------------------*)
let trivial t = match t with 
  | Trivial -> ()
  | NonTrivial _ -> failwith "impossible"

let conj_guard g1 g2 = match g1, g2 with 
  | Trivial, g
  | g, Trivial -> g
  | NonTrivial f1, NonTrivial f2 -> NonTrivial (Util.mk_conj f1 f2)

let rec close_forall bs f = 
  List.fold_right (fun b f -> 
    let body = mk_Typ_lam([b], f) (mk_Kind_arrow([b], ktype) f.pos) f.pos in
    match fst b with 
       | Inl a -> 
          mk_Typ_app(Util.tforall_typ a.sort, [targ body]) ktype f.pos
       | Inr x -> 
          mk_Typ_app(Util.tforall, [(Inl x.sort, true); targ body]) ktype f.pos) bs f

let close_guard binders g = match g with 
    | Trivial -> g
    | NonTrivial f -> close_forall binders f |> NonTrivial

let mk_guard g ps slack = {guard_f=g; carry=List.map snd ps; slack=slack}

(* ------------------------------------------------*)
(* </guard_formula ops>                            *)
(* ------------------------------------------------*)

(* ------------------------------------------------*)
(* <prob ops> lifting from problem to prob         *)
(* ------------------------------------------------*)
let invert_rel = function 
    | EQ -> EQ
    | SUB -> SUBINV
    | SUBINV -> SUB
let invert p       = {p with lhs=p.rhs; rhs=p.lhs; relation=invert_rel p.relation}
let maybe_invert p = if p.relation = SUBINV then invert p else p
let p_rel = function 
   | KProb p -> p.relation
   | TProb p -> p.relation
   | EProb p -> p.relation
   | CProb p -> p.relation    
let p_reason = function 
   | KProb p -> p.reason
   | TProb p -> p.reason
   | EProb p -> p.reason
   | CProb p -> p.reason    
let p_loc = function 
   | KProb p -> p.loc
   | TProb p -> p.loc
   | EProb p -> p.loc
   | CProb p -> p.loc
let p_context = function
   | KProb p -> p.closing_context
   | TProb p -> p.closing_context
   | EProb p -> p.closing_context
   | CProb p -> p.closing_context
let mk_problem orig lhs rel rhs elt bs reason = {     
     lhs=lhs;
     relation=rel;
     rhs=rhs;
     element=elt;
     closing_context=bs@p_context orig;
     reason=reason::p_reason orig;
     loc=p_loc orig;
     }
(* ------------------------------------------------*)
(* </prob ops>                                     *)
(* ------------------------------------------------*)

(* ------------------------------------------------*)
(* <worklist ops> Operations on worklists          *)
(* ------------------------------------------------*)
let empty_worklist = {
    attempting=[];
    deferred=[];
    subst=[];
    guard=Trivial;
    ctr=0;
    slack_vars=[];
    defer_ok=true;
}
let singleton prob         = {empty_worklist with attempting=[prob]}
let extend_subst' uis wl   = {wl with subst=uis@wl.subst; ctr=wl.ctr + 1}
let extend_subst ui wl     = {wl with subst=ui::wl.subst; ctr=wl.ctr + 1}
let defer prob wl          = {wl with deferred=(wl.ctr, prob)::wl.deferred}
let attempt probs wl       = {wl with attempting=probs@wl.attempting}
let guard (env:env) g wl   = {wl with guard=conj_guard g wl.guard}   
let add_slack slack wl     = {wl with slack_vars=slack@wl.slack_vars}
let giveup env reason prob = 
    if debug env <| Options.Other "Rel"
    then Util.fprint2 "Failed %s:\n%s\n" reason (prob_to_string env prob);
    Failed(prob, reason)
(* ------------------------------------------------*)
(* </worklist ops>                                 *)
(* ------------------------------------------------*)

(* ------------------------------------------------*)
(* <uvi ops> Instantiating unification variables   *)
(* ------------------------------------------------*)
let commit env uvis = 
    uvis |> List.iter (function
        | UK(u,k)     -> Unionfind.change u (Fixed k)
        | UT((u,k),t) -> if debug env (Options.Other "Rel")
                         then Util.fprint2 "Commiting %s to %s\n" (Print.uvar_t_to_string (u,k)) (Normalize.typ_norm_to_string env t);
                         Unionfind.change u (Fixed t)
        | UE((u,_),e) -> Unionfind.change u (Fixed e)
        | UC((u,_),c) -> Unionfind.change u (Fixed c))

let find_uvar_k uv s = Util.find_map s (function UK(u, t) ->     if Unionfind.equivalent uv u then Some t else None | _ -> None)
let find_uvar_t uv s = Util.find_map s (function UT((u,_), t) -> if Unionfind.equivalent uv u then Some t else None | _ -> None)
let find_uvar_e uv s = Util.find_map s (function UE((u,_), t) -> if Unionfind.equivalent uv u then Some t else None | _ -> None)
let find_uvar_c uv s = Util.find_map s (function UC((u,_), t) -> if Unionfind.equivalent uv u then Some t else None | _ -> None)
(* ------------------------------------------------*)
(* </uvi ops>                                      *)
(* ------------------------------------------------*)


(* ------------------------------------------------*)
(* <normalization>                                *)
(* ------------------------------------------------*)
let norm_targ env t = Tc.Normalize.norm_typ [Beta] env t
let norm_arg env a = match fst a with 
    | Inl t -> Inl <| norm_targ env t, snd a
    | Inr v -> Inr <| Tc.Normalize.norm_exp [Beta] env v, snd a
let whnf env t = Tc.Normalize.whnf env t |> Util.compress_typ
let sn env t = Tc.Normalize.norm_typ [Beta;Eta] env t |> Util.compress_typ
let sn_binders env binders = 
    binders |> List.map (function 
        | Inl a, imp -> 
          Inl ({a with sort=Tc.Normalize.norm_kind [Beta] env a.sort}), imp
        | Inr x, imp -> 
          Inr ({x with sort=norm_targ env x.sort}), imp)
let whnf_k env k = Tc.Normalize.norm_kind [Beta;Eta;WHNF] env k |> Util.compress_kind

let rec compress_k (env:env) wl k = 
    let k = Util.compress_kind k in 
    match k.n with 
        | Kind_uvar(uv, actuals) -> 
            (match find_uvar_k uv wl.subst with
                | None -> k
                | Some k' -> 
                    match k'.n with 
                        | Kind_lam(formals, body) -> 
                               let k = Util.subst_kind (Util.subst_of_list formals actuals) body in
                               compress_k env wl k
                        | _ -> if List.length actuals = 0 
                               then compress_k env wl k'
                               else failwith "Wrong arity for kind unifier")
        | _ -> k

let rec compress env wl t =
    let t = Util.unmeta_typ t in
    match t.n with 
        | Typ_uvar (uv, _) ->
           (match find_uvar_t uv wl.subst with 
                | None -> whnf env t
                | Some t -> compress env wl t)   
        | Typ_app({n=Typ_uvar(uv, _)}, args) -> 
            (match find_uvar_t uv wl.subst with 
                | Some t' -> 
                  let t' = compress env wl t' in 
                  let t'' = mk_Typ_app(t', args) t.tk t.pos in 
                  whnf env t'' 
                | _ -> whnf env t)
        | _ -> whnf env t

let rec compress_e (env:env) wl e = 
    let e = Util.unmeta_exp e in
    match e.n with 
        | Exp_uvar (uv, t) -> 
           begin match find_uvar_e uv wl.subst with 
            | None -> e
            | Some e' -> compress_e env wl e'
           end
        | Exp_app({n=Exp_uvar(uv, _)}, args) -> 
           begin match find_uvar_e uv wl.subst with 
            | None -> e
            | Some e' -> 
                let e' = compress_e env wl e' in
                mk_Exp_app(e', args) e.tk e.pos //TODO: whnf for expressions?
           end
        | _ -> e

let normalize_refinement env wl t0 = 
   let t = Normalize.norm_typ [Normalize.DeltaHard] env (compress env wl t0) in
   let rec aux t = 
    let t = Util.compress_typ t in
    match t.n with
       | Typ_refine(x, phi) -> 
            let t0 = aux x.sort in
            begin match t0.n with 
              | Typ_refine(y, phi1) ->
                mk_Typ_refine(y, Util.mk_conj phi1 (Util.subst_typ [Inr(x.v, Util.bvar_to_exp y)] phi)) ktype t0.pos
              | _ -> t
            end
       | _ -> t in
   aux t

let base_and_refinement env wl t1 =
   let rec aux norm t1 =
        match t1.n with 
        | Typ_refine(x, phi) -> 
            if norm 
            then (x.sort, Some(x, phi))
            else begin match normalize_refinement env wl t1 with
                | {n=Typ_refine(x, phi)} -> (x.sort, Some(x, phi))
                | _ -> failwith "impossible"
            end

        | Typ_const _
        | Typ_app _ -> 
            if norm 
            then (t1, None)
            else aux true (normalize_refinement env wl t1)

        | Typ_btvar _
        | Typ_fun _
        | Typ_lam _ -> (t1, None)

        | Typ_ascribed _
        | Typ_uvar _
        | Typ_delayed _
        | Typ_meta _
        | Typ_unknown -> failwith "impossible" in
   aux false t1

(* ------------------------------------------------ *)
(* </normalization>                                 *)
(* ------------------------------------------------ *)

(* ------------------------------------------------ *)
(* <variable ops> common ops on variables           *)
(* ------------------------------------------------ *)
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

let occurs_and_freevars_check env uk fvs t = 
    let fvs_t = Util.freevars_typ t in
    let occurs_ok, msg = occurs_check env uk t in
    occurs_ok && Util.fvs_included fvs_t fvs

let occurs_check_e env ut e = 
    let uvs = Util.uvars_in_exp e in 
    let occurs_ok = not (Util.set_mem ut uvs.uvars_e) in
    let msg = 
        if occurs_ok then None
        else Some (Util.format3 "occurs-check failed (%s occurs in {%s} uvars of %s normalized to %s)" 
                        (Print.uvar_e_to_string ut) 
                        (Util.set_elements uvs.uvars_e |> List.map Print.uvar_e_to_string |> String.concat ", ")
                        (Normalize.exp_norm_to_string env e)) in
    occurs_ok, msg


let intersect_vars v1 v2 = 
    let fvs1 = freevars_of_binders v1 in
    let fvs2 = freevars_of_binders v2 in 
    binders_of_freevars ({ftvs=Util.set_intersect fvs1.ftvs fvs2.ftvs; fxvs=Util.set_intersect fvs1.fxvs fvs2.fxvs})

let binders_eq v1 v2 = 
  List.length v1 = List.length v2 
  && List.forall2 (fun ax1 ax2 -> match fst ax1, fst ax2 with 
        | Inl a, Inl b -> Util.bvar_eq a b
        | Inr x, Inr y -> Util.bvar_eq x y
        | _ -> false) v1 v2

let rec pat_vars env seen args : option<binders> = match args with 
    | [] -> Some (List.rev seen) 
    | hd::rest -> 
        (match fst <| norm_arg env hd with
            | Inl {n=Typ_btvar a} -> 
               if seen |> Util.for_some (function 
                        | Inl b, _ -> bvd_eq a.v b.v
                        | _ -> false)
               then None //not a pattern
               else pat_vars env ((Inl a, snd hd)::seen) rest

            | Inr {n=Exp_bvar x} ->
                if seen |> Util.for_some (function 
                    | Inr y, _ -> bvd_eq x.v y.v
                    | _ -> false)
                then None //not a pattern
                else pat_vars env ((Inr x, snd hd)::seen) rest

            | _ -> None) //not a pattern

let destruct_flex_t t = match t.n with
    | Typ_uvar(uv, k) -> (t, uv, k, [])
    | Typ_app({n=Typ_uvar(uv, k)}, args) -> (t, uv, k, args)
    | _ -> failwith "Not a flex-uvar"
(* ------------------------------------------------ *)
(* </variable ops>                                  *)
(* ------------------------------------------------ *)


(* ------------------------------------------------ *)
(* <decomposition> of a type/kind with its binders  *)
(* ------------------------------------------------ *)
(* ///////////////////////////////////////////////////
   A summary of type decomposition
   ///////////////////////////////////////////////////
   
   It simplifies the unification algorithm to view every F* term/type/kind
   as either a lambda, a variable, or the application of a constructor to some arguments.
    
   For the built-in term formers, i.e., Typ_fun, Typ_refine, and Kind_arrow, 
   we need a way to decompose them into their sub-terms so that they 
   appear in the form (C arg1 ... argn), for some constructor C.
     
   We call this operation 'decomposition'.

   To illustrate, take:

   val decompose_typ: env -> typ 
                    -> (list<ktec> -> typ) 
                        * (typ -> bool) 
                        * list<(binders * ktec)>

   let recompose, matches, components = decompose_typ env t
        
        1. The components are the immediate sub-terms of t, 
           with their contexts provided as a binders
           
           For example: if t = x1:t1 -> ... -> xn:tn -> C
           the components are ([([], t1); ... ([(x1..xn-1)], tn); ([(x1..xn)], C)]

        2. recompose is a function that rebuilds a t-like type from new subterms
           
           In our example, rebuild [s1;...;sn; C'] builds
                           x1:s1 -> ... -> xn:sn -> C'
           The shape of the argument to rebuild must match the shape of the components of t

        3. matches is function which decides whether or not 
           a given type t' could be structurally similar to t (modulo reduction). It serves
           as a proxy for the constructor C itself

           For example, any Typ_fun full matches t
                        any Uvar    head matches t
                        any Typ_lam head matches t
                        any (t1 t2) head matches t, if t1 matches t
              
           where t matches t' 
              if t head matches t'
              or t full matches t'
*)

type match_result = 
  | MisMatch
  | HeadMatch
  | FullMatch

let head_match = function 
    | MisMatch -> MisMatch
    | _ -> HeadMatch

let rec head_matches env t1 t2 : match_result = 
  match (Util.unmeta_typ t1).n, (Util.unmeta_typ t2).n with 
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

    | _, Typ_lam _ -> HeadMatch
   
    | _ -> MisMatch

let decompose_binder (bs:binders) ktec_v (rebuild_base:binders -> ktec -> 'a) : ((list<ktec> -> 'a)          //recompose
                                                                                 * list<(binders * ktec)>) = //components
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
 
let rec decompose_kind (env:env) (k:knd) : (list<ktec> -> knd) * list<(binders * ktec)> = 
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
    let t = Util.unmeta_typ t in
    let matches t' = head_matches env t t' <> MisMatch in
    match t.n with 
        | Typ_app(hd, args) -> (* easy case: it's already in the form we want *)
          let rebuild args' = 
            let args = List.map2 (fun x y -> match x, y with
                | (Inl _, imp), T t -> Inl t, imp
                | (Inr _, imp), E e -> Inr e, imp
                | _ -> failwith "Bad reconstruction") args args' in
            mk_Typ_app(hd, args) t.tk t.pos in
        
          let b_ktecs = //each argument in order, with empty binders
            args |> List.map (function (Inl t, _) -> [], T t | (Inr e, _) -> [], E e) in
        
          rebuild, matches, b_ktecs

        | Typ_fun(bs, c) -> 
          let rebuild, b_ktecs = 
              decompose_binder bs (C c) (fun bs -> function 
                | C c -> mk_Typ_fun(bs, c) ktype t.pos
                | _ -> failwith "Bad reconstruction") in
          
          rebuild, matches, b_ktecs

        | Typ_refine(x, phi) -> 
          let rebuild, b_ktecs = 
              decompose_binder [v_binder x] (T phi) (fun bs tt -> match bs, tt with 
                | [(Inr y, _)], T phi' -> mk_Typ_refine(y, phi') ktype t.pos
                | _ -> failwith "Bad reconstruction") in
          
          rebuild, matches, b_ktecs
        

        | _ -> 
          let rebuild = function
            | [] -> t
            | _ -> failwith "Bad reconstruction" in

          rebuild, (fun t -> true), []

(* Does t1 match t2, after some delta steps? *)
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

(* ------------------------------------------------ *)
(* </decomposition>                                 *)
(* ------------------------------------------------ *)

(* ------------------------------------------------ *)
(* <slack> Destructing formulas for slack variables *)
(* ------------------------------------------------ *)

(* /////////////////////////////////////////////////////
   A summary of the treatment of slack 
   /////////////////////////////////////////////////////

   When solving a refinement subtyping constraint involving a unification variable U, 
   we solve U with a type of the shape x:t{slack_formula x}
   where slack_formula x has the shape

       (F \/ p+ xs) /\ (G /\ q* xs)

   We call the left conjunct a lower bound---it reflects the strongest logical 
   property we obtain for U, and is built from subtyping constraints of the form t <: U.
   We call p+ an additive slack variable.

   The right conjunct is an upper bound---it reflects the weakest logical property
   that must hold for U. It is build from subtyping constraints of the form U <: t.
   We call q* a multiplicative slack variable.

   Subtyping constraints involving unification variables and refinement formulas introduce 
   and propagate slack variables in a manner that ensures that the subtyping constraints are satisfiable, 
   given the validity of a logical guard.

   At the top-level of a derivation, all the remaining uninstantiated slack variables are collected. 
   Every positive variable p+ is instantiated to \xs.False
   Every negative variable q* is instantiated to \xs.True

   An invariant of the system is, given the validity of the logical constraints emitted, the 
   lower bound of the system always implies the upper bound.

   For readability, we will write a slack formula as
   
          Lower(F, p xs) /\ Upper(G, q xs)
   
   
1. Slack-intro-T-flex: Given a subtyping problem, with a uvar on the right:
           
            t <: u xs

    if t is not an arrow, not a lambda, then normalize the problem to the form

            x:t'{phi x} <: u xs

    where t' has no non-trivial super types.
    
    Then set 
            u = \xs. x:t'{Lower(phi x, p x) /\ Upper(True /\ q x)})
 
    Solve it by imitating the rhs, while introducing a slack formula, 
    recording phi as a lower bound.

2. Slack-intro-fun-flex: Given 

        t <: u ys , where t is an arrow type

   Normalize it to 

        f:(x:t1 -> M (t2 x)){phi f} <: u ys
   
   And solve it using

        u = \ys. f:(x:u1 ys -> M (u2 ys x)){Lower(phi, p ys f) /\ Upper(True /\ q ys f)}
   
   producing subtyping constraints

          u1 ys <: t1
    and   t2 x  <: u2 ys x
       
   This rule would enable the inferring types for constructs like:
        
        [f:nat -> Tot int;
         g:int -> Tot nat;
         h:pos -> Tot pos] : list (pos -> Tot int)

   A similar rule applies for type-lambdas
 
3. Slack-intro-flex-T: Given 
    
        u xs <: t    where t is not an arrow type
        
   Normalize t and solve

        u xs <: x:t'{phi}
   
   by imitating 

        u xs = \xs. x:t'{Lower(False \/ p xs x) /\ Upper(phi x, q xs x)}

4. Slack-intro-flex-fun: Given

      u ys <: t      where t is an arrow type

   Normalize t and solve

      u ys <: f:(x:t1 -> M (t2 x)){phi f}
   
   by imitating

      u = \ys. f:(x:u1 ys -> M (u2 ys x){Lower(False \/ p xs f) /\ Upper(phi f, q xs f)} 
               

5. Slack-refine: Given

          x:t{Lower(phi1, p xs) /\ Upper(phi2, q xs)} <: t'

   Normalize the RHS, where psi is slack-free:
   
          x:t{Lower(phi1, p xs) /\ Upper(phi2, q xs)} <: y:s{psi}

   And solve by:

    1. t <: s

    2. Generate phi ==> psi[x/y]

    3. Instantiate q = \xs. psi[x/y] /\ q' xs, for a fresh slack variable q'

6. Refine-Slack: Given

         t' <: x:t{Lower(phi1, p xs) /\ Upper(phi2, q xs)} 

   Normalize the RHS, where psi is slack-free:
   
         y:s{psi} <: x:t{Lower(phi1, p xs) /\ Upper(phi2, q xs)}

   And solve by:

   1. s <: t

   2. Generate psi[x/y] ==> phi2

   3. Instantiate p = \xs. psi[x/y] \/ p' xs, for fresh slack variable p'

7. Slack-Slack:

      x:t1{Lower(phi1, p1 xs) /\ Upper(psi1, q1 xs)} <: y:t2{Lower(phi2, p2 xs) /\ Upper(psi2, q2 xs)}

   1. t1 <: t2

   2 a. p1 = \xs. phi2 \/ p xs
   2 b. p2 = \xs. phi1 \/ p xs

   3 a. q1 = \xs. psi2 /\ q xs
   3 b. q2 = \xs. psi1 /\ q xs

   4 a. phi1 ==> psi2
   4 b. phi2 ==> psi1



3 a. Slack-elim-L-pos: Given
            x:t{Pos(phi \/ slack x)}  <: x:t{phi'} 
       where phi' may or may not have slack
               
       Solve by:
            slack = \x. Neg(phi' /\ slack' x) 

       And producing the logical constraint:
            forall x. phi x ==> phi' x

       Intuitively, by flipping the polarity of the slack and guarding it with phi', 
       we ensure that any further weakening instantiations of the slack cannot weaken it 
       beyond the desired bound phi'.

3 b. Slack-elim-L-neg: Given
            x:t{Neg(phi \/ (psi /\ slack x))}  <: x:t{phi'} 
       where phi' may or may not have slack
               
       Solve by:
            slack = \x. Neg(phi' /\ slack' x) 

       And producing the logical constraint:
            forall x. phi x ==> phi' x

4. Slack-reintro-R: Given
           x:t{phi} <: x:t{slack x \/ phi'}
       where phi does not have slack

       Solve by setting
           slack = \x. slack' x \/ phi x
       for fresh slack'

5. No-Slack-L: Given
      
       u <: t

   Solve it by setting u = t

   No point in leaving slack on the LHS, since t is a lower-bound anyway

We carry all slack variables to the top-level. After solving all constraints,
if there are any remaining slack variables, we set them all to \xs.False.

Note, the case where both side have slack, is covered by case 3:
       Consider:
           x:t{slack1 x \/ phi1} <: x:t2{slack2 \/ phi2}
        
       Solve by:
           slack1 = \x. slack2 x \/ phi2

       And 
           forall x. phi1 x ==> (slack2 x \/ phi2 x) *)


(* 
  A refinement formula phi may include a slack variable
  If it does, phi always has the shape:
      ((u x1..xn \/ phi1) \/ phi2 ... \/ phin)
  where u is the slack variable
  For such a phi, destruct slack returns
  Some (u x1..xn, (phi1 \/ phi2 \/ ... \/ phin))
*)
let destruct_slack env wl (phi:typ) : option<(typ * typ)> = 
   let rec aux disjuncts phi = 
      match (compress env wl phi).n with
        | Typ_app({n=Typ_const tc}, [(Inl lhs, _);(Inl rhs, _)]) 
            when (lid_equals tc.v Const.or_lid) -> 
            let lhs = compress env wl lhs in
            begin match lhs.n with
                | Typ_uvar _ 
                | Typ_app({n=Typ_uvar _}, _) -> 
                  //found slack variable
                  Some (lhs, Util.mk_disj_l (rhs::disjuncts))
                | _ ->
                  aux (rhs::disjuncts) lhs
            end
        | _ -> None in
    aux [] phi

(* ------------------------------------------------ *)
(* </slack>                                         *)
(* ------------------------------------------------ *)

(* ------------------------------------------------ *)
(* <solver> The main solving algorithm              *)
(* ------------------------------------------------ *)
type flex_t = (typ * uvar_t * knd * args)
type im_or_proj_t = ((uvar_t * knd) * list<arg> * binders * ((list<ktec> -> typ) * (typ -> bool) * list<(binders * ktec)>))
         
let rec solve (env:Tc.Env.env) (probs:worklist) : solution = 
//    printfn "Solving TODO:\n%s;;" (List.map prob_to_string probs.attempting |> String.concat "\n\t");
    match probs.attempting with 
       | hd::tl -> 
         let probs = {probs with attempting=tl} in
         begin match hd with 
            | KProb kp -> solve_k env (maybe_invert kp) probs
            | TProb tp -> solve_t env (maybe_invert tp) probs
            | EProb ep -> solve_e env (maybe_invert ep) probs
            | CProb cp -> solve_c env (maybe_invert cp) probs
         end
       | [] ->
         match probs.deferred with 
            | [] -> Success (probs.subst, mk_guard probs.guard [] probs.slack_vars) //Yay ... done!
            | _ -> 
              let attempt, rest = probs.deferred |> List.partition (fun (c, _) -> c < probs.ctr) in
              match attempt with 
                 | [] -> Success(probs.subst, mk_guard probs.guard probs.deferred probs.slack_vars) //can't solve yet; defer the rest
                 | _ -> solve env ({probs with attempting=attempt |> List.map snd; deferred=rest})


and solve_binders (env:Tc.Env.env) (bs1:binders) (bs2:binders) (orig:prob) (wl:worklist) 
                  (rhs:list<subst_elt> -> binders -> prob) : solution =
   let rec aux subprobs prefix subst bs1 bs2 = match bs1, bs2 with 
        | [], [] -> 
          let probs = subprobs@[rhs subst bs1] in
          solve env (attempt probs wl)

        | hd1::tl1, hd2::tl2 -> 
            begin match fst hd1, fst hd2 with 
                | Inl a, Inl b -> 
                  let prob = KProb <| mk_problem orig (Util.subst_kind subst b.sort) (p_rel orig) a.sort None prefix "Formal type parameter" in
                  aux (prob::subprobs) (prefix@[hd1]) (mk_subst_binder hd1 hd2 subst) tl1 tl2

                | Inr x, Inr y ->
                  let prob = TProb <| mk_problem orig (Util.subst_typ subst y.sort) (p_rel orig) x.sort None prefix "Formal value parameter" in
                  aux (prob::subprobs) (prefix@[hd1]) (mk_subst_binder hd1 hd2 subst) tl1 tl2

                | _ -> giveup env "non-corresponding binders" orig
            end

        | _ -> giveup env "arrow arity" orig  in

       aux [] [] [] bs1 bs2

and solve_k (env:Env.env) (problem:problem<knd,typ>) (wl:worklist) : solution =
    if Util.physical_equality problem.lhs problem.rhs then solve env wl else
    let k1 = compress_k env wl problem.lhs in 
    let k2 = compress_k env wl problem.rhs in
    if Util.physical_equality k1 k2 then solve env wl else
    let r = Env.get_range env in 

    let imitate_k (rel, u, ps, xs, (h, qs)) =
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
              let prob = 
                let lhs, rhs = gi_ps, ki in
                mk_problem (KProb problem) lhs rel rhs None binders "kind subterm" in
              K gi_xs, KProb prob

            | binders, T ti ->  
              let gi_xs, gi = new_tvar r (xs@binders) ti.tk in
              let gi_ps = mk_Typ_app(gi, ps) ti.tk r in
              let prob = 
                let lhs, rhs = gi_ps, ti in
                mk_problem (KProb problem) lhs rel rhs None binders "type subterm" in
              T gi_xs, TProb prob) |> List.unzip in

        let im = mk_Kind_lam(xs, h gs_xs) r in
        let wl = extend_subst (UK(u, im)) wl in 
        solve env (attempt sub_probs wl) in

    let flex_rigid rel u args k = 
        let maybe_vars1 = pat_vars env [] args in
        match maybe_vars1 with 
          | Some xs -> 
            let fvs1 = freevars_of_binders xs in
            let fvs2 = Util.freevars_kind k2 in
            let uvs2 = Util.uvars_in_kind k2 in
            if Util.set_is_subset_of fvs2.ftvs fvs1.ftvs
                && Util.set_is_subset_of fvs2.fxvs fvs1.fxvs
                && not(Util.set_mem u uvs2.uvars_k)
            then let k1 = mk_Kind_lam(xs, k2) r in //Solve in one-step
                solve env (extend_subst (UK(u, k1)) wl)
            else imitate_k (rel, u, xs |> Util.args_of_non_null_binders, xs, decompose_kind env k) 

          | None -> 
            giveup env ("flex-rigid: not a pattern") (KProb problem) in
           
    match k1.n, k2.n with 
     | Kind_type, Kind_type 
     | Kind_effect, Kind_effect -> solve env wl

     | Kind_abbrev(_, k1), _ -> solve_k env ({problem with lhs=k1}) wl
     | _, Kind_abbrev(_, k2) -> solve_k env ({problem with rhs=k2}) wl

     | Kind_arrow(bs1, k1'), Kind_arrow(bs2, k2') -> 
       let sub_prob subst bs = 
           KProb <| mk_problem (KProb problem) k1' problem.relation (Util.subst_kind subst k2') None bs "Arrow-kind result"  in
       solve_binders env bs1 bs2 (KProb problem) wl sub_prob

     | Kind_uvar(u1, args1), Kind_uvar (u2, args2) -> //flex-flex: at the kind level, we only solve patterns anyway
       let maybe_vars1 = pat_vars env [] args1 in
       let maybe_vars2 = pat_vars env [] args2 in
       begin match maybe_vars1, maybe_vars2 with 
            | None, _
            | _, None -> giveup env "flex-flex: non patterns" (KProb problem)
            | Some xs, Some ys -> 
              if Unionfind.equivalent u1 u2 && binders_eq xs ys
              then solve env wl
              else  //U1 xs =?= U2 ys
                    //zs = xs intersect ys, U fresh
                    //U1 = \xs. U zs
                    //U2 = \ys. U zs(KP
                  let zs = intersect_vars xs ys in
                  let u, _ = new_kvar r zs in 
                  let k1 = mk_Kind_lam(xs, u) r in
                  let k2 = mk_Kind_lam(ys, u) r in
                  solve env <| extend_subst' [UK(u1, k1); UK(u2, k2)] wl 
       end

     | Kind_uvar (u, args), _ -> 
       flex_rigid problem.relation u args k2 
         
     | _, Kind_uvar (u, args) -> 
       flex_rigid (invert_rel problem.relation) u args k1

     | Kind_delayed _, _ 
     | Kind_unknown, _
     | _, Kind_delayed _ 
     | _, Kind_unknown -> failwith "Impossible"

     | _ -> giveup env "head mismatch (k-1)" (KProb problem)

and solve_t (env:Env.env) (problem:problem<typ,exp>) (wl:worklist) : solution =
    let orig = TProb problem in
    let giveup_or_defer msg = 
        if wl.defer_ok
        then solve env (defer orig wl)
        else giveup env msg orig in 


    (* <flex-rigid> *)
    let solve_t_flex_rigid (lhs:flex_t) (t2:typ) = 
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
                else giveup env "head-symbol is free" orig probs in
   (* </flex-rigid> *)

   (* <flex-flex>: 
      Always interpret a flex-flex constraint as an equality, even if it is tagged as SUB/SUBINV
      This causes a loss of generality. Consider:

        nat <: u1 <: u2
        int <: u2
        u1 <: nat

      By collapsing u1 and u2, the constraints become unsolveable, since we then have
        nat <: u <: nat and int <: u

      However, it seems unlikely that this would arise in practice. TBD.
 
      The alternative is to delay all flex-flex subtyping constraints, even the pattern cases. 
      But, it seems that performance would suffer greatly then. TBD.
   *)
   let flex_flex (lhs:flex_t) (rhs:flex_t) : solution = 
        let (t1, u1, k1, args1) = lhs in
        let (t2, u2, k2, args2) = rhs in 
        let maybe_pat_vars1 = pat_vars env [] args1 in
        let maybe_pat_vars2 = pat_vars env [] args2 in
        let r = t2.pos in
        let solve_one_pat (t1, u1, k1, xs) (t2, u2, k2, args2) = 
            if Tc.Env.debug env <| Options.Other "Rel"
            then Util.fprint2 "Trying flex-flex one pattern (%s) with %s\n" (Print.typ_to_string t1) (Print.typ_to_string t2);
            let t2 = sn env t2 in
            let rhs_vars = Util.freevars_typ t2 in
            let occurs_ok, _ = occurs_check env (u1,k1) t2 in
            let lhs_vars = freevars_of_binders xs in
            if occurs_ok && Util.fvs_included rhs_vars lhs_vars
            then let sol = UT((u1, k1), mk_Typ_lam'(xs, t2) k1 t1.pos) in
                 solve env (extend_subst sol wl)
            else giveup_or_defer "flex-flex (one pattern) occurs-check or free variable check" in
     
        let solve_both_pats xs ys = 
            if Unionfind.equivalent u1 u2 && binders_eq xs ys
            then solve env wl
            else //U1 xs =?= U2 ys
                 //zs = xs intersect ys, U fresh
                 //U1 = \x1 x2. U zs
                 //U2 = \y1 y2 y3. U zs
                let xs = sn_binders env xs in
                let ys = sn_binders env ys in
                let zs = intersect_vars xs ys in
                let u_zs, _ = new_tvar r zs t2.tk in
                let sub1 = mk_Typ_lam'(xs, u_zs) k1 r in
                let occurs_ok, msg = occurs_check env (u1,k1) sub1 in
                if not occurs_ok
                then giveup_or_defer "flex-flex: failed occcurs check" 
                else let sol1 = UT((u1, k1), sub1) in
                     if Unionfind.equivalent u1 u2
                     then solve env (extend_subst sol1 wl)
                     else let sub2 = mk_Typ_lam'(ys, u_zs) k2 r in
                          let occurs_ok, msg = occurs_check env (u2,k2) sub2 in
                          if not occurs_ok 
                          then giveup_or_defer "flex-flex: failed occurs check"
                          else let sol2 = UT((u2,k2), sub2) in
                               solve env (extend_subst' [sol1;sol2] wl) in

      
         match maybe_pat_vars1, maybe_pat_vars2 with 
            | Some xs, Some ys -> solve_both_pats xs ys
            | Some xs, None -> solve_one_pat (t1, u1, k1, xs) rhs
            | None, Some ys -> solve_one_pat (t2, u2, k2, ys) lhs
            | _ -> 
              if wl.defer_ok
              then solve env (defer orig wl)
              else giveup env "flex-flex constraint" orig in
    (* </flex-flex> *)

    (* <slack-intro-1> *)
    let slack_intro_1 (x, phi) (rhs, u, k, args) =
        let maybe_pat_vars = pat_vars env [] args in
        match maybe_pat_vars with 
            | None -> 
              if wl.defer_ok
              then solve env (defer orig wl)
              else solve_t env (invert ({problem with relation=EQ})) wl  //it's not a pattern; rather than giving up, try solving it as a flex-rigid equality

            | Some xs -> 
              let slack_pat, slack_var = new_tvar problem.rhs.pos (v_binder x::xs) ktype in
              let imitate = mk_Typ_refine(x, Util.mk_disj phi slack_pat) ktype problem.rhs.pos in
              if occurs_and_freevars_check env (u,k) (freevars_of_binders xs) imitate 
              then let sol = UT((u,k), mk_Typ_lam(xs, imitate) k problem.rhs.pos) in
                   solve env (extend_subst sol wl)
              else if wl.defer_ok
              then solve env (defer orig wl)
              else solve_t env (invert ({problem with relation=EQ})) wl  in //it's not a pattern; rather than giving up, try solving it as a flex-rigid equality
    (* </slack-intro-1> *)

    if Util.physical_equality problem.lhs problem.rhs then solve env wl else
    let t1 = compress env wl problem.lhs in
    let t2 = compress env wl problem.rhs in 
    if Util.physical_equality t1 t2 then solve env wl else
    let _ = 
        if debug env (Options.Other "Rel") 
        then Util.fprint1 "Attempting %s\n" (prob_to_string env <| TProb problem) in
    let r = Env.get_range env in
 
    let match_num_binders (bs1, mk_cod1) (bs2, mk_cod2) =
        let curry n bs mk_cod = 
            let bs, rest = Util.first_N n bs in
            (bs, mk_cod rest) in
            
        let l1 = List.length bs1 in
        let l2 = List.length bs2 in
        if l1 = l2
        then (bs1, mk_cod1 []),    
             (bs2, mk_cod2 [])
        else if l1 > l2
        then curry l2 bs1 mk_cod1, 
             (bs2, mk_cod2 []) 
        else (bs1, mk_cod1 []),    
             curry l1 bs2 mk_cod2 in

    match t1.n, t2.n with
      | Typ_btvar a, Typ_btvar b -> 
        if Util.bvd_eq a.v b.v 
        then solve env wl
        else giveup env "unequal type variables" orig(* TODO: They may be equal by refinement, though *)
         
      | Typ_fun(bs1, c1), Typ_fun(bs2, c2) ->
        let mk_c c = function
            | [] -> c
            | bs -> mk_Total(mk_Typ_fun(bs, c) ktype c.pos) in
        let (bs1, c1), (bs2, c2) = 
            match_num_binders (bs1, mk_c c1) (bs2, mk_c c2) in
        solve_binders env bs1 bs2 orig wl
        (fun subst binders -> 
            let c2 = Util.subst_comp subst c2 in
            let rel = if !Options.verify then EQ else problem.relation in
            CProb <| mk_problem orig c1 rel c2 None binders "function co-domain")

      | Typ_lam(bs1, t1'), Typ_lam(bs2, t2') -> 
        let mk_t t = function
            | [] -> t
            | bs -> mk_Typ_lam(bs, t) (mk_Kind_arrow(bs, t.tk) t.pos) t.pos in
        let (bs1, t1'), (bs2, t2') = 
            match_num_binders (bs1, mk_t t1') (bs2, mk_t t2') in
        solve_binders env bs1 bs2 orig wl
        (fun subst binders -> 
            let t2' = Util.subst_typ subst t2' in
            TProb <| mk_problem orig t1 problem.relation t2' None binders "lambda co-domain")

      | Typ_refine _, Typ_refine _ -> 
        let t1 = normalize_refinement env wl t1 in
        let t2 = normalize_refinement env wl t2 in
        begin match t1.n, t2.n with 
            | Typ_refine(x1, phi1), Typ_refine(x2, phi2) -> 
              let base_prob = TProb <| mk_problem orig x1.sort problem.relation x2.sort problem.element [] "refinement base type" in
              let x1_for_x2 = mk_subst_binder (v_binder x1) (v_binder x2) [] in
              let mk_imp imp phi1 phi2 = 
                let phi2' = Util.subst_typ x1_for_x2 phi2 in
                let phi1_imp_phi2 = imp phi1 phi2 in
                let imp = match problem.element with 
                    | None -> close_forall (v_binder x1::problem.closing_context) phi1_imp_phi2
                    | Some e -> close_forall problem.closing_context <| Util.subst_typ ([Inr(x1.v, e)]) phi1_imp_phi2 in
                imp, phi2' in
             
              begin match problem.relation with
                  | EQ -> 
                    let impl, _ = mk_imp Util.mk_iff phi1 phi2 in
                    let wl = guard env (NonTrivial impl) wl in
                    solve env (attempt [base_prob] wl)

                  | SUB -> 
                    begin match (destruct_slack env wl phi1, destruct_slack env wl phi2) with
                        | None, None ->  (* standard refinement subtyping; no slack on either side *)
                          let impl, _ = mk_imp Util.mk_imp phi1 phi2 in
                          let wl = guard env (NonTrivial impl) wl in
                          solve env (attempt [base_prob] wl)

                        | Some (slack1, phi1), _ ->  (* slack on the-left: use Slack-elim-L *)  
                          let impl, phi2' = mk_imp Util.mk_imp phi1 phi2 in
                          let wl = guard env (NonTrivial impl) wl in 
                          let slack_prob = TProb <| mk_problem orig slack1 EQ phi2' None [v_binder x1] "slack variable (Slack-elim-L)" in
                          solve env (attempt [base_prob; slack_prob] wl)

                        | None, Some(slack2, phi2) -> (* slack on the right but not on the left: use Slack-reintro-R *)
                          let _, u, k, args = destruct_flex_t slack2 in
                          begin match pat_vars env [] args with 
                            | None -> giveup env "slack variable is not a pattern" orig
                            | Some xs ->
                              let slack2_1, slack_var_1 = new_tvar slack2.pos xs ktype in
                              let slack2_2, slack_var_2 = new_tvar slack2.pos xs ktype in
                              let sol = UT((u,k), mk_Typ_lam(xs, Util.mk_disj slack2_1 slack2_2) k slack2.pos) in
                              let sub_prob = 
                                let phi1 = Util.subst_typ (mk_subst_binder (v_binder x2) (v_binder x1) []) phi1 in
                                TProb <| mk_problem orig slack2_2 EQ phi2 None [v_binder x2] "slack variable (Slack-reintro-R)" in
                              let wl = add_slack [slack_var_1; slack_var_2] wl |> extend_subst sol in
                              solve env (attempt [base_prob; sub_prob] wl)
                          end
                    end
    
                | SUBINV -> failwith "impossible"
            end
          | _ -> failwith "impossible"
       end
         
      (* flex-flex *)
      | Typ_uvar _,                 Typ_uvar _
      | Typ_app({n=Typ_uvar _}, _), Typ_uvar _ 
      | Typ_uvar _,                 Typ_app({n=Typ_uvar _}, _)
      | Typ_app({n=Typ_uvar _}, _), Typ_app({n=Typ_uvar _}, _) -> 
        flex_flex (destruct_flex_t t1) (destruct_flex_t t2) 
   
      (* flex-rigid *)
      | Typ_uvar _, _
      | Typ_app({n=Typ_uvar _}, _), _ -> 
        (* Even if this is a subtyping constraint, solve it as an equality, without loss of generality, 
           since the rigid type on the RHS is already a lower bound *)
        solve_t_flex_rigid (destruct_flex_t t1) t2 

      (* rigid-flex: reorient if it is an equality constraint *)
      | _, Typ_uvar _ 
      | _, Typ_app({n=Typ_uvar _}, _) when (problem.relation = EQ) ->
        solve_t env (invert problem) wl

      (* rigid-flex: subtyping *)
      | _, Typ_uvar _ 
      | _, Typ_app({n=Typ_uvar _}, _) when (problem.relation = EQ) ->
        let t_base, refinement = base_and_refinement env wl t1 in
        begin match refinement with 
             | None -> 
               (* 
                  No interesting refinement on t1; default to using solve using Rigid-flex-SUBEQ 
                   i.e., t1 <: t1' <==> t1' = t1; (except for the caveat of function types). 
                  So, in this case, we may as well treat the constraint as an equality and reorient. 
               *)
               solve_t env ({problem with lhs=t2; rhs=t_base; relation=EQ}) wl

             | Some (x, phi) ->  
               slack_intro_1 (x, phi) (destruct_flex_t t2)
        end

 
      | Typ_refine(x, phi1), _ ->
        begin match base_and_refinement env wl t2 with 
            | (t_base, None) -> 
               solve_t env ({problem with lhs=x.sort; rhs=t_base}) wl

            | (_, Some (y, phi2)) ->
               let rhs = mk_Typ_refine(y, phi2) ktype t2.pos in
               solve_t env ({problem with rhs=rhs}) wl
        end

      | _, Typ_refine(x, phi2) -> 
        begin match base_and_refinement env wl t1 with 
            | (t_base, None) -> 

               solve_t env ({problem with lhs=x.sort; rhs=t_base}) wl

            | (_, Some (y, phi1)) ->
               let lhs = mk_Typ_refine(y, phi1) ktype t1.pos in
               solve_t env ({problem with lhs=lhs}) wl
        end


        if rel=EQ
        then giveup env "refinement subtyping is not applicable" (TProb(top, rel, t1, t2)) wl //but t1 may be able to take delta steps
        else let g = NonTrivial <| mk_Typ_lam([v_binder (bvd_to_bvar_s x.v t1)], phi2) (mk_Kind_arrow([null_v_binder t1], ktype) r) r in
             solve_t top env rel t1 x.sort (guard env top g wl)   
      
      | Typ_btvar _, _
      | Typ_const _, _
      | Typ_app _, _
      | _, Typ_btvar _
      | _, Typ_const _ 
      | _, Typ_app _ -> 
         let m, o = head_matches_delta env t1 t2 in
         begin match m, o  with 
            | (MisMatch, _) -> 
                giveup env "head mismatch (t-1)" (TProb(top, rel, t1, t2)) wl        //heads definitely do not match

            | (_, Some (t1, t2)) ->
               //              printfn "Head match with delta %s, %s" (Print.typ_to_string head) (Print.typ_to_string head');
               wl |> solve_t top env rel t1 t2

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
                    solve env (attempt subprobs wl)
                else giveup env (Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" 
                            (Print.typ_to_string head)
                            (Print.args_to_string args)
                            (Print.typ_to_string head')
                            (Print.args_to_string args')) 
                            (TProb(top, rel, t1, t2)) wl
          end

      | Typ_ascribed _ , _
      | Typ_meta _, _ 
      | Typ_delayed _, _
      | _, Typ_ascribed _
      | _, Typ_meta _
      | _, Typ_delayed _ -> failwith "Impossible"

      | _ -> giveup env "head mismatch" <| TProb problem

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
                          aux (List.rev all_xs) (List.rev args1)
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


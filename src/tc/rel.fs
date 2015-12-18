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
module FStar.Tc.Rel

open FStar
open FStar.Options
open FStar.Tc
open FStar.Absyn
open FStar.Absyn.Util
open FStar.Util
open FStar.Tc.Env
open FStar.Tc.Normalize
open FStar.Absyn.Syntax


(* --------------------------------------------------------- *)
(* <new_uvar> Generating new unification variables/patterns  *)
(* --------------------------------------------------------- *)
let new_kvar r binders =
  let u = Unionfind.fresh Uvar in
  mk_Kind_uvar (u, Util.args_of_non_null_binders binders) r, u

let new_tvar r binders k =
  let binders = binders |> List.filter (fun x -> is_null_binder x |> not) in
  let uv = Unionfind.fresh Uvar in
  match binders with
    | [] ->
      let uv = mk_Typ_uvar'(uv,k) None r in
      uv, uv
    | _ ->
      let args = Util.args_of_non_null_binders binders in
      let k' = mk_Kind_arrow(binders, k) r in
      let uv = mk_Typ_uvar'(uv,k') None r in
      mk_Typ_app(uv, args) None r, uv

let new_evar r binders t =
  let binders = binders |> List.filter (fun x -> is_null_binder x |> not) in
  let uv = Unionfind.fresh Uvar in
  match binders with
    | [] ->
      let uv = mk_Exp_uvar'(uv,t) None r in
      uv, uv
    | _ ->
      let args = Util.args_of_non_null_binders binders in
      let t' = mk_Typ_fun(binders, mk_Total t) None r in
      let uv = mk_Exp_uvar'(uv, t') None r in
      match args with
        | [] -> uv, uv
        | _ -> mk_Exp_app(uv, args) None r, uv

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

type variance =
    | COVARIANT
    | CONTRAVARIANT
    | INVARIANT

type problem<'a,'b> = {               //Try to prove: lhs rel rhs ~> guard
    lhs:'a;
    relation:rel;
    rhs:'a;
    element:option<'b>;               //where, guard is a predicate on this term (which appears free in/is a subterm of the guard)
    logical_guard:(typ * typ);        //the condition under which this problem is solveable, and the uvar that underlies it
    scope:binders;                    //the set of names permissible in the guard of this formula
    reason: list<string>;             //why we generated this problem, for error reporting
    loc: Range.range;                 //and the source location where this arose
    rank: option<int>;
}
type problem_t<'a,'b> = problem<'a,'b>

type prob =
  | KProb of problem<knd,unit>
  | TProb of problem<typ,exp>
  | EProb of problem<exp,unit>
  | CProb of problem<comp,unit>

type probs = list<prob>

(* Instantiation of unification variables *)
type uvi =
  | UK of uvar_k * knd
  | UT of (uvar_t * knd) * typ
  | UE of (uvar_e * typ) * exp

(* The set of problems currently being addressed *)
type worklist = {
    attempting: probs;
    wl_deferred:   list<(int * string * prob)>;  //flex-flex cases, non patterns, and subtyping constraints involving a unification variable,
    subst:      list<uvi>;                    //the partial solution derived so far
    ctr:        int;                          //a counter incremented each time we extend subst, used to detect if we've made progress
    slack_vars: list<(bool * typ)>;           //all the slack variables introduced so far, the flag marks a multiplicative variable
    defer_ok:   bool;                         //whether or not carrying constraints is ok---at the top-level, this flag is false
    smt_ok:     bool;                         //whether or not falling back to the SMT solver is permitted
    tcenv:      Tc.Env.env;
}

(* Types used in the output of the solver *)
type deferred = {
  carry:   list<(string * prob)>;
  slack:   list<(bool * typ)>;
}
let no_deferred = {
    carry=[];
    slack=[];
}
type solution =
  | Success of list<uvi> * deferred
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
    Util.format "\t%s (%s) \n\t\t%s(%s)\n\t%s (%s) (guard %s)"
        [(Normalize.typ_norm_to_string env p.lhs);
         (Print.tag_of_typ p.lhs);
         (rel_to_string p.relation);
         (p.reason |> List.hd);
         (Normalize.typ_norm_to_string env p.rhs);
         (Print.tag_of_typ p.rhs);
         (Normalize.formula_norm_to_string env (fst p.logical_guard))]
  | EProb p -> Util.format3 "\t%s \n\t\t%s\n\t%s" (Normalize.exp_norm_to_string env p.lhs) (rel_to_string p.relation) (Normalize.exp_norm_to_string env p.rhs)
  | CProb p -> Util.format3 "\t%s \n\t\t%s\n\t%s" (Normalize.comp_typ_norm_to_string env p.lhs) (rel_to_string p.relation) (Normalize.comp_typ_norm_to_string env p.rhs)

let uvi_to_string env uvi =
  (* By design. F* does not generalize inner lets by default. *)
  let str (u:Unionfind.uvar<'a>) = if !Options.hide_uvar_nums then "?" else Unionfind.uvar_id u |> string_of_int in
  match uvi with
      | UK (u, _) -> str u |> Util.format1 "UK %s"
      | UT ((u,_), t) -> str u |> (fun x -> Util.format2 "UT %s %s" x (Normalize.typ_norm_to_string env t))
      | UE ((u,_), _) -> str u |> Util.format1 "UE %s"

(* ------------------------------------------------*)
(* </Printing> *)
(* ------------------------------------------------*)

(* ------------------------------------------------*)
(* <prob/problem ops                               *)
(* ------------------------------------------------*)
let invert_rel = function
    | EQ -> EQ
    | SUB -> SUBINV
    | SUBINV -> SUB
let invert p       = {p with lhs=p.rhs; rhs=p.lhs; relation=invert_rel p.relation}
let maybe_invert p = if p.relation = SUBINV then invert p else p
let maybe_invert_p = function
    | KProb p -> maybe_invert p |> KProb
    | TProb p -> maybe_invert p |> TProb
    | EProb p -> maybe_invert p |> EProb
    | CProb p -> maybe_invert p |> CProb
let vary_rel rel = function
    | INVARIANT -> EQ
    | CONTRAVARIANT -> invert_rel rel
    | COVARIANT -> rel
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
   | KProb p -> p.scope
   | TProb p -> p.scope
   | EProb p -> p.scope
   | CProb p -> p.scope
let p_guard = function
   | KProb p -> p.logical_guard
   | TProb p -> p.logical_guard
   | EProb p -> p.logical_guard
   | CProb p -> p.logical_guard
let p_scope = function
   | KProb p -> p.scope
   | TProb p -> p.scope
   | EProb p -> p.scope
   | CProb p -> p.scope
let p_invert = function
   | KProb p -> KProb <| invert p
   | TProb p -> TProb <| invert p
   | EProb p -> EProb <| invert p
   | CProb p -> CProb <| invert p
let is_top_level_prob p = p_reason p |> List.length = 1

let mk_problem scope orig lhs rel rhs elt reason = {
     lhs=lhs;
     relation=rel;
     rhs=rhs;
     element=elt;
     logical_guard=new_tvar (p_loc orig) scope ktype;
     scope=[];
     reason=reason::p_reason orig;
     loc=p_loc orig;
     rank=None;
}
let new_problem env lhs rel rhs elt loc reason = {
    lhs=lhs;
    relation=rel;
    rhs=rhs;
    element=elt;
    logical_guard=new_tvar (Env.get_range env) (Env.binders env) ktype;
    scope=[];
    reason=[reason];
    loc=loc;
    rank=None;
}
let problem_using_guard orig lhs rel rhs elt reason = {
     lhs=lhs;
     relation=rel;
     rhs=rhs;
     element=elt;
     logical_guard=p_guard orig;
     scope=[];
     reason=reason::p_reason orig;
     loc=p_loc orig;
     rank=None;
}
let guard_on_element problem x phi =
    match problem.element with
        | None ->   close_forall [v_binder x] phi
        | Some e -> Util.subst_typ ([Inr(x.v, e)]) phi
let solve_prob' resolve_ok prob logical_guard uvis wl =
    let phi = match logical_guard with
      | None -> Util.t_true
      | Some phi -> phi in
    let _, uv = p_guard prob in
    let _ = match (Util.compress_typ uv).n with
        | Typ_uvar(uvar, k) ->
          let phi = Util.close_for_kind phi k in
          Util.unchecked_unify uvar phi
        | _ -> if not resolve_ok then failwith "Impossible: this instance has already been assigned a solution" in
    match uvis with
        | [] -> wl
        | _ ->
        if Tc.Env.debug wl.tcenv <| Options.Other "Rel"
        then Util.print1 "Extending solution: %s\n" (List.map (uvi_to_string wl.tcenv) uvis |> String.concat ", ");
        {wl with subst=uvis@wl.subst; ctr=wl.ctr + 1}

let extend_solution sol wl = {wl with subst=sol::wl.subst; ctr=wl.ctr+1}
let solve_prob prob logical_guard uvis wl = solve_prob' false prob logical_guard uvis wl
let explain env d s =
    Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
                       (Range.string_of_range <| p_loc d)
                       (prob_to_string env d)
                       (p_reason d |> String.concat "\n\t>")
                       s

(* ------------------------------------------------*)
(* </prob ops>                                     *)
(* ------------------------------------------------*)


(* ------------------------------------------------*)
(* <worklist ops> Operations on worklists          *)
(* ------------------------------------------------*)
let empty_worklist env = {
    attempting=[];
    wl_deferred=[];
    subst=[];
    ctr=0;
    slack_vars=[];
    tcenv=env;
    defer_ok=true;
    smt_ok=true
}
let singleton env prob     = {empty_worklist env with attempting=[prob]}
let wl_of_guard env g      = {empty_worklist env with defer_ok=false; attempting=List.map snd g.carry; slack_vars=g.slack}
let defer reason prob wl   = {wl with wl_deferred=(wl.ctr, reason, prob)::wl.wl_deferred}
let attempt probs wl       = {wl with attempting=probs@wl.attempting}
let add_slack_mul slack wl = {wl with slack_vars=(true, slack)::wl.slack_vars}
let add_slack_add slack wl = {wl with slack_vars=(false, slack)::wl.slack_vars}

let giveup env reason prob =
    if debug env <| Options.Other "Rel"
    then Util.print2 "Failed %s:\n%s\n" reason (prob_to_string env prob);
    Failed(prob, reason)
(* ------------------------------------------------*)
(* </worklist ops>                                 *)
(* ------------------------------------------------*)

(* ------------------------------------------------*)
(* <uvi ops> Instantiating unification variables   *)
(* ------------------------------------------------*)
let commit env uvis =
    uvis |> List.iter (function
        | UK(u,k)     -> Util.unchecked_unify u k
        | UT((u,k),t) -> Util.unchecked_unify u t
        | UE((u,_),e) -> Util.unchecked_unify u e)

let find_uvar_k uv s = Util.find_map s (function UK(u, t) ->     if Unionfind.equivalent uv u then Some t else None | _ -> None)
let find_uvar_t uv s = Util.find_map s (function UT((u,_), t) -> if Unionfind.equivalent uv u then Some t else None | _ -> None)
let find_uvar_e uv s = Util.find_map s (function UE((u,_), t) -> if Unionfind.equivalent uv u then Some t else None | _ -> None)
(* ------------------------------------------------*)
(* </uvi ops>                                      *)
(* ------------------------------------------------*)


(* ------------------------------------------------*)
(* <normalization>                                *)
(* ------------------------------------------------*)
let simplify_formula env f = Normalize.norm_typ [Beta; Simplify] env f
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
let whnf_e env e = Tc.Normalize.norm_exp [Beta;Eta;WHNF] env e |> Util.compress_exp

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
    let t = whnf env (Util.unmeta_typ t) in
    match t.n with
        | Typ_uvar (uv, _) ->
           (match find_uvar_t uv wl.subst with
                | None -> t
                | Some t -> compress env wl t)
        | Typ_app({n=Typ_uvar(uv, _)}, args) ->
            (match find_uvar_t uv wl.subst with
                | Some t' ->
                  let t = mk_Typ_app(t', args) None t.pos in
                  compress env wl t
                | _ -> t)
        | _ -> t

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
                mk_Exp_app(e', args) None e.pos //TODO: whnf for expressions?
           end
        | _ -> e

let normalize_refinement steps env wl t0 = Normalize.normalize_refinement steps env (compress env wl t0)

let base_and_refinement env wl t1 =
   let rec aux norm t1 =
        match t1.n with
        | Typ_refine(x, phi) ->
            if norm
            then (x.sort, Some(x, phi))
            else begin match normalize_refinement [] env wl t1 with
                | {n=Typ_refine(x, phi)} -> (x.sort, Some(x, phi))
                | tt -> failwith (Util.format2 "impossible: Got %s ... %s\n" (Print.typ_to_string tt) (Print.tag_of_typ tt))
            end

        | Typ_const _
        | Typ_app _ ->
            if norm
            then (t1, None)
            else let t2', refinement = aux true (normalize_refinement [] env wl t1) in
                 begin match refinement with
                    | None -> t1, None (* no refinement found ... so revert to the original type, without expanding defs *)
                    | _ -> t2', refinement
                 end

        | Typ_btvar _
        | Typ_fun _
        | Typ_lam _
        | Typ_uvar _ -> (t1, None)

        | Typ_ascribed _
        | Typ_delayed _
        | Typ_meta _
        | Typ_unknown -> failwith (Util.format2 "impossible (outer): Got %s ... %s\n" (Print.typ_to_string t1) (Print.tag_of_typ t1)) in
   aux false (compress env wl t1)

let unrefine env t = base_and_refinement env (empty_worklist env) t |> fst

let trivial_refinement t = Util.gen_bvar_p t.pos t, Util.t_true

let as_refinement env wl t =
    let t_base, refinement = base_and_refinement env wl t in
    match refinement with
        | None -> trivial_refinement t_base

        | Some (x, phi) ->
            x, phi

let force_refinement (t_base, refopt) =
    let y, phi = match refopt with
        | Some (y, phi) -> y, phi
        | None -> trivial_refinement t_base in
    mk_Typ_refine(y, phi) None t_base.pos

(* ------------------------------------------------ *)
(* </normalization>                                 *)
(* ------------------------------------------------ *)

(* ------------------------------------------------ *)
(* <variable ops> common ops on variables           *)
(* ------------------------------------------------ *)
let rec occurs (env:'a) (wl:worklist) (uk:(uvar_t * 'b)) (t:typ) =
    let uvs = Util.uvars_in_typ t in
    uvs.uvars_t |> Util.set_elements |> Util.for_some (fun (uvt, _) ->
        match find_uvar_t uvt wl.subst with
            | None -> Unionfind.equivalent uvt (fst uk)
            | Some t ->
               let t = match Util.compress_typ t with
                        | {n=Typ_lam(_, t)} -> t
                        | t -> t in
              occurs env wl uk t)

let occurs_check env wl uk t =
    let occurs_ok = not (occurs env wl uk t) in
    let msg =
        if occurs_ok then None
        else Some (Util.format3 "occurs-check failed (%s occurs in %s) (with substitution %s)"
                        (Print.uvar_t_to_string uk)
                        (Print.typ_to_string t)
                        (wl.subst |> List.map (uvi_to_string env) |> String.concat ", ")) in
    occurs_ok, msg

let occurs_and_freevars_check env wl uk fvs t =
    let fvs_t = Util.freevars_typ t in
    let occurs_ok, msg = occurs_check env wl uk t in
    (occurs_ok, Util.fvs_included fvs_t fvs, (msg, fvs, fvs_t))

let occurs_check_e env ut e =
    let uvs = Util.uvars_in_exp e in
    let occurs_ok = not (Util.set_mem ut uvs.uvars_e) in
    let msg =
        if occurs_ok then None
        else Some (Util.format3 "occurs-check failed (%s occurs in {%s} uvars of %s)"
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

let pat_var_opt env seen arg =
   let hd = norm_arg env arg in
   match fst <| hd with
    | Inl {n=Typ_btvar a} ->
        if seen |> Util.for_some (function
                    | Inl b, _ -> bvd_eq a.v b.v
                    | _ -> false)
        then None
        else Some (Inl a, snd hd)

    | Inr {n=Exp_bvar x} ->
        if seen |> Util.for_some (function
            | Inr y, _ -> bvd_eq x.v y.v
            | _ -> false)
        then None
        else Some (Inr x, snd hd)

    | _ -> None

let rec pat_vars env seen args : option<binders> = match args with
    | [] -> Some (List.rev seen)
    | hd::rest ->
        begin match pat_var_opt env seen hd with
            | None -> if Tc.Env.debug env <| Options.Other "Rel" then Util.print1 "Not a pattern: %s\n" (Print.arg_to_string hd); None //not a pattern
            | Some x -> pat_vars env (x::seen) rest
        end

let destruct_flex_t t = match t.n with
    | Typ_uvar(uv, k) -> (t, uv, k, [])
    | Typ_app({n=Typ_uvar(uv, k)}, args) -> (t, uv, k, args)
    | _ -> failwith "Not a flex-uvar"

let destruct_flex_e e = match e.n with
    | Exp_uvar(uv, k) -> (e, uv, k, [])
    | Exp_app({n=Exp_uvar(uv, k)}, args) -> (e, uv, k, args)
    | _ -> failwith "Not a flex-uvar"

let destruct_flex_pattern env t =
    let (t, uv, k, args) = destruct_flex_t t in
    match pat_vars env [] args with
        | Some vars -> (t, uv, k, args), Some vars
        | _ -> (t, uv, k, args), None
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
                        * list<(option<binder> * variance * ktec)>

   let recompose, matches, components = decompose_typ env t

        1. The components are the immediate sub-terms of t,
           with their contexts provided as a binders

           For example: if t = x1:t1 -> ... -> xn:tn -> C
           the components are ([(Some x1, CONTRAVARIANT, t1); ... ([Some xn, CONTRAVARIANT, tn); ([None, COVARIANT, C)]

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

let rec head_matches t1 t2 : match_result =
  match (Util.unmeta_typ t1).n, (Util.unmeta_typ t2).n with
    | Typ_btvar x, Typ_btvar y -> if Util.bvar_eq x y then FullMatch else MisMatch
    | Typ_const f, Typ_const g -> if Util.fvar_eq f g then FullMatch else MisMatch

    | Typ_btvar _, Typ_const _
    | Typ_const _, Typ_btvar _ -> MisMatch

    | Typ_refine(x, _), Typ_refine(y, _) -> head_matches x.sort y.sort |> head_match

    | Typ_refine(x, _), _  -> head_matches x.sort t2 |> head_match
    | _, Typ_refine(x, _)  -> head_matches t1 x.sort |> head_match

    | Typ_fun _, Typ_fun _  -> HeadMatch

    | Typ_app(head, _), Typ_app(head', _) -> head_matches head head'
    | Typ_app(head, _), _ -> head_matches head t2
    | _, Typ_app(head, _) -> head_matches t1 head

    | Typ_uvar (uv, _),  Typ_uvar (uv', _) -> if Unionfind.equivalent uv uv' then FullMatch else MisMatch

    | _, Typ_lam _ -> HeadMatch

    | _ -> MisMatch

(* Does t1 match t2, after some delta steps? *)
let head_matches_delta env wl t1 t2 : (match_result * option<(typ*typ)>) =
    let success d r t1 t2 = (r, (if d>0 then Some(t1, t2) else None)) in
    let fail () = (MisMatch, None) in
    let rec aux d t1 t2 =
        match head_matches t1 t2 with
            | MisMatch ->
                if d=2 then fail() //already delta normal
                else if d=1 then 
                     let t1' = normalize_refinement [Normalize.UnfoldOpaque] env wl t1 in
                     let t2' = normalize_refinement [Normalize.UnfoldOpaque] env wl t2 in
                     aux 2 t1' t2'
                else let t1 = normalize_refinement [] env wl t1 in
                     let t2 = normalize_refinement [] env wl t2 in
                     aux (d+1) t1 t2
            | r -> success d r t1 t2 in
    aux 0 t1 t2

let decompose_binder (bs:binders) v_ktec (rebuild_base:binders -> ktec -> 'a) : ((list<ktec> -> 'a)                            //recompose
                                                                                 * list<(option<binder> * variance * ktec)>) = //components
    let fail () = failwith "Bad reconstruction" in
    let rebuild ktecs =
        let rec aux new_bs bs ktecs = match bs, ktecs with
            | [], [ktec] -> rebuild_base (List.rev new_bs) ktec
            | (Inl a, imp)::rest, K k::rest' -> aux ((Inl ({a with sort=k}), imp)::new_bs) rest rest'
            | (Inr x, imp)::rest, T (t, _)::rest' -> aux ((Inr ({x with sort=t}), imp)::new_bs) rest rest'
            | _ -> fail () in
        aux [] bs ktecs in

    let rec mk_b_ktecs (binders, b_ktecs) = function
        | [] -> List.rev ((None, COVARIANT, v_ktec)::b_ktecs)
        | hd::rest ->
            let bopt = if is_null_binder hd then None else Some hd in
            let b_ktec = match fst hd with
                | Inl a -> (bopt, CONTRAVARIANT, K a.sort)
                | Inr x -> (bopt, CONTRAVARIANT, T (x.sort, Some ktype)) in
            let binders' = match bopt with None -> binders | Some hd -> binders@[hd] in
            mk_b_ktecs (binders', b_ktec::b_ktecs) rest in

    rebuild, mk_b_ktecs ([], []) bs

let rec decompose_kind (env:env) (k:knd) : (list<ktec> -> knd) * list<(option<binder> * variance * ktec)> =
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


let rec decompose_typ env t : (list<ktec> -> typ) * (typ -> bool) * list<(option<binder> * variance * ktec)> =
    let t = Util.unmeta_typ t in
    let matches t' = head_matches t t' <> MisMatch in
    match t.n with
        | Typ_app(hd, args) -> (* easy case: it's already in the form we want *)
          let rebuild args' =
            let args = List.map2 (fun x y -> match x, y with
                | (Inl _, imp), T (t, _) -> Inl t, imp
                | (Inr _, imp), E e -> Inr e, imp
                | _ -> failwith "Bad reconstruction") args args' in
            mk_Typ_app(hd, args) None t.pos in

          let b_ktecs = //each argument in order, with empty binders
            args |> List.map (function (Inl t, _) -> None, INVARIANT, T (t, None) | (Inr e, _) -> None, INVARIANT, E e) in

          rebuild, matches, b_ktecs

        | Typ_fun(bs, c) ->
          let rebuild, b_ktecs =
              decompose_binder bs (C c) (fun bs -> function
                | C c -> mk_Typ_fun(bs, c) None t.pos
                | _ -> failwith "Bad reconstruction") in

          rebuild, matches, b_ktecs

        | _ ->
          let rebuild = function
            | [] -> t
            | _ -> failwith "Bad reconstruction" in

          rebuild, (fun t -> true), []

let un_T = function
    | T (x, _) -> x
    | _ -> failwith "impossible"
let arg_of_ktec = function
    | T (t, _) -> targ  t
    | E e -> varg e
    | _ -> failwith "Impossible"

let imitation_sub_probs orig env scope (ps:args) (qs:list<(option<binder> * variance * ktec)>) =
   //U p1..pn REL h q1..qm
   //if h is not a free variable
   //extend_subst: (U -> \x1..xn. h (G1(x1..xn), ..., Gm(x1..xm)))
   //sub-problems: Gi(p1..pn) REL' qi, where REL' = vary_rel REL (variance h i)
    let r = p_loc orig in
    let rel = p_rel orig in
    let sub_prob scope args q =
        match q with
        | _, variance, K ki ->
            let gi_xs, gi = new_kvar r scope in
            let gi_ps = mk_Kind_uvar(gi, args) r in
            K gi_xs,
            KProb <| mk_problem scope orig gi_ps (vary_rel rel variance) ki None "kind subterm"

        | _, variance, T (ti, kopt) ->
            let k = match kopt with
                | Some k -> k
                | None -> Recheck.recompute_kind ti in
            let gi_xs, gi = new_tvar r scope k in
            let gi_ps = mk_Typ_app'(gi, args) None r in
            T (gi_xs, Some k),
            TProb <| mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm"

        | _, variance, E ei ->
            let t = Recheck.recompute_typ ei in
            let gi_xs, gi = new_evar r scope t in
            let gi_ps = mk_Exp_app'(gi, args) (Some t) r in
            E gi_xs,
            EProb <| mk_problem scope orig gi_ps (vary_rel rel variance) ei None "expression subterm"

        | _, _, C _ -> failwith "impos" in

    let rec aux scope args qs : (list<prob> * list<ktec> * formula) =
        match qs with
            | [] -> [], [], Util.t_true
            | q::qs ->
                let ktec, probs = match q with
                     | bopt, variance, C ({n=Total ti}) ->
                       begin match sub_prob scope args (bopt, variance, T (ti, Some ktype)) with
                            | T (gi_xs, _), prob -> C <| mk_Total gi_xs, [prob]
                            | _ -> failwith "impossible"
                       end

                    |_, _, C ({n=Comp c}) ->
                       let components = c.effect_args |> List.map (function
                            | Inl t, _ -> (None, INVARIANT, T (t, None))
                            | Inr e, _ -> (None, INVARIANT, E e)) in
                       let components = (None, COVARIANT, T (c.result_typ, Some ktype))::components in
                       let ktecs, sub_probs = List.map (sub_prob scope args) components |> List.unzip in
                       let gi_xs = mk_Comp <| {
                            effect_name=c.effect_name;
                            result_typ=List.hd ktecs |> un_T;
                            effect_args=List.tl ktecs |> List.map arg_of_ktec;
                            flags=c.flags
                        }  in
                        C gi_xs, sub_probs

                    | _ ->
                      let ktec, prob = sub_prob scope args q in
                      ktec, [prob] in

                let bopt, scope, args = match q with
                    | Some b, _, _ -> Some b, b::scope, arg_of_non_null_binder b::args
                    | _ -> None, scope, args in

                let sub_probs, ktecs, f = aux scope args qs in
                let f = match bopt with
                    | None -> Util.mk_conj_l (f:: (probs |> List.map (fun prob -> p_guard prob |> fst)))
                    | Some b -> Util.mk_conj_l (close_forall [b] f:: (probs |> List.map (fun prob -> p_guard prob |> fst))) in
                probs@sub_probs, ktec::ktecs, f in

   aux scope ps qs

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

   For readability, we will write a slack formula as

          Lower(F, p xs) /\ Upper(G, q xs)

   Subtyping constraints involving unification variables and refinement formulas introduce
   and propagate slack variables in a manner that ensures that the subtyping constraints are satisfiable,
   given the validity of a logical guard.

   At the top-level of a derivation, all the remaining uninstantiated slack variables are collected.
   Every additive variable p+ is instantiated to \xs.False
   Every multiplicative variable q* is instantiated to \xs.True

   An invariant of the system is, given the validity of the logical constraints emitted, the
   lower bound of the system always implies the upper bound.


1. Slack-intro-T-flex: Given a subtyping problem, with a uvar on the right:

            t <: u xs

    if t is not an arrow, not a lambda, then normalize the problem to the form

            x:t'{phi x} <: u xs

    where t' has no non-trivial super types.

    Then set:
            u = \xs. x:t'{Lower(phi x, p x) /\ Upper(True /\ q x)})

    i.e., solve it by imitating the rhs, while introducing a slack formula,
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

    2. Generate phi1 ==> psi[x/y]

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

    if  uvars(phi1, p1) does not contain p2
    and uvars(psi2, q2) does not contain q1

    1. t1 <: t2

    2. p2 = \xs. (phi1 \/ p1 xs) \/ p2' xs    (moving lower bound up)

    3. q1 = \xs. (psi2 /\ q2 xs) /\ q2'. xs   (moving upper bound down)

    4. phi1 ==> psi2                          (perserving invariant)

    i.e., someting analogous to doing both Slack-Refine and Refine-Slack


Some alternatives:

   2* a. p2 = \xs. phi1 \/ p xs   for fresh p
   3* a. phi1 ==> psi2

   Note, you might consider an alternative strategy:

   2* b. q1 = \xs. phi2 /\ q xs   for fresh q
   3* b. phi1 ==> phi2

   2* c.
   However, the (b) strategy is not complete. For example:

   nat <: u1 <: u2 <: int
   pos <: u2

   Using the (a) strategy, we solve with the following steps:
     1. u1 = x:int{Lower(x>=0, p1 x), Upper(q1 x)}                 [Slack-intro-T-flex]
     2. u2 = x:int{Lower(x>0, p2 x),  Upper(q2 x)}                 [Slack-intro-T-flex]
     3. u2 = x:int{Lower(x>0 \/ x>=0, p2' x), Upper(q2 x)}         [Slack-slack-a]
     4. u2 = x:int{Lower(x>0 \/ x>=0, p2' x), Upper(true, q2' x)}  [Slack-refine]

   Using the (b) strategy, we have:
     1. u1 = x:int{Lower(x>=0, p1 x), Upper(q1 x)}
     2. u2 = x:int{Lower(x>0, p2 x),  Upper(q2 x)}
     3. u1 = x:int{Lower(x>=0, p1 x), Upper(x>0, q2' x)}         //Which is unsatisfiable
     4. u2 = x:int{Lower(x>0, p2 x),  Upper(true, q2' x)}

   But (a) is unsound:

     nat <: u1 <: u2 <: nat
     pos <: u2
     neg <: u1

   Using the (a) strategy, we solve with use the first three steps above, then:
     4. u2 = x:int{Lower(x>0 \/ x>=0, p2' x), Upper(x>=0, q2' x)}  [Slack-refine]
     5. u1 = x:int{Lower(x>=0 \/ x<0, p1' x), Upper(q1 x)}  ... but u1 </: u2

*)
type slack = {lower:(typ * typ);
              upper:(typ * typ);
              flag:ref<bool>}  //second component of each pair is a flex term

(* removing slack *)
let fix_slack_uv (uv,k) mul =
    let inst = if mul
                then Util.close_for_kind Util.t_true k
                else Util.close_for_kind Util.t_false k in
    Util.unchecked_unify uv inst

let fix_slack_vars slack =
    slack |> List.iter (fun (mul, s) -> match (Util.compress_typ s).n with
        | Typ_uvar(uv, k) -> fix_slack_uv (uv,k) mul
        | _ -> ())

let fix_slack slack =
    let (_, ul, kl, _) = destruct_flex_t <| snd slack.lower in
    let (_, uh, kh, _) = destruct_flex_t <| snd slack.upper in
    fix_slack_uv (ul,kl) false;
    fix_slack_uv (uh,kh) true;
    slack.flag := true;
    Util.mk_conj (fst slack.lower) (fst slack.upper)

let new_slack_var env slack =
    let xs = destruct_flex_pattern env (snd slack.lower) |> snd |> Util.must in
    new_tvar (fst slack.lower).pos xs ktype, xs

let new_slack_formula p env wl xs low high =
    let low_var, uv1 = new_tvar p xs ktype in
    let wl = add_slack_add uv1 wl in
    let high_var, uv2 = new_tvar p xs ktype in
    let wl = add_slack_mul uv2 wl in
    let low = match low with
        | None -> Util.mk_disj Util.t_false low_var
        | Some f -> Util.mk_disj f low_var in
    let high = match high with
        | None -> Util.mk_conj Util.t_true high_var
        | Some f -> Util.mk_conj f high_var in
    mk_Typ_meta(Meta_slack_formula(low, high, Util.mk_ref false)), wl

(*
  A refinement formula phi may include a slack variable
     Typ_meta(Meta_slack_formula(lower, upper))
  where lower has the shape
      (phi1 \/ phi2 \/ ... \/ u xs)
  and upper has the shape
      (phi1 /\ phi2 /\ ... /\ u xs)
  destruct_slack parses a slack formula into
    {lower: (phi1 \/ phi2 \/ ... \/ phin, u xs);
     upper: (phi1 /\ phi2 /\ ... /\ phin, u xs)}
*)
let destruct_slack env wl (phi:typ) : either<typ, slack> =
   let rec destruct conn_lid mk_conn phi =
    match phi.n with
        | Typ_app({n=Typ_const tc}, [(Inl lhs, _); (Inl rhs, _)])
            when (lid_equals tc.v conn_lid) ->
            let rhs = compress env wl rhs in
            begin match rhs.n with
                | Typ_uvar _
                | Typ_app({n=Typ_uvar _}, _) -> //found slack variable
                  Some (lhs, rhs)
                | _ ->
                  begin match destruct conn_lid mk_conn rhs with
                            | None -> None
                            | Some (rest, uvar) -> Some (mk_conn lhs rest, uvar)
                  end
            end
        | _ -> None in

   let phi = Util.compress_typ phi in
   match phi.n with
    | Typ_meta(Meta_slack_formula(phi1, phi2, flag)) ->
      if !flag
      then Inl (Util.unmeta_typ phi)
      else let low = destruct Const.or_lid Util.mk_disj <| compress env wl phi1 in
           let hi  = destruct Const.and_lid Util.mk_disj  <| compress env wl phi2 in
           begin match low, hi with
                  | None, None ->  flag := true; Inl (Util.unmeta_typ phi)
                  | Some _, None
                  | None, Some _ -> failwith "Impossible"
                  | Some l, Some u -> Inr ({lower=l; upper=u; flag=flag})
           end

    | _ -> Inl phi
(* ------------------------------------------------ *)
(* </slack>                                         *)
(* ------------------------------------------------ *)

(* ---------------------------------------------------------------------- *)
(* <eq_args> Special case of deciding syntactic equality, an optimization *)
(* ---------------------------------------------------------------------- *)
let rec eq_typ (t1:typ) (t2:typ) =
    let t1 = compress_typ t1 in
    let t2 = compress_typ t2 in
    match t1.n, t2.n with
        | Typ_btvar a, Typ_btvar b -> Util.bvar_eq a b
        | Typ_const f, Typ_const g -> Util.fvar_eq f g
        | Typ_uvar (u1, _), Typ_uvar (u2, _) -> Unionfind.equivalent u1 u2
        | Typ_app (h1, args1), Typ_app(h2, args2) ->
          eq_typ h1 h2 && eq_args args1 args2
        | _ -> false
and eq_exp (e1:exp) (e2:exp) =
    let e1 = compress_exp e1 in
    let e2 = compress_exp e2 in
    match e1.n, e2.n with
        | Exp_bvar a, Exp_bvar b -> Util.bvar_eq a b
        | Exp_fvar (f, _), Exp_fvar (g, _) -> Util.fvar_eq f g
        | Exp_constant c, Exp_constant d -> c=d
        | Exp_app(h1, args1), Exp_app(h2, args2) -> eq_exp h1 h2 && eq_args args1 args2
        | _ -> false
and eq_args (a1:args) (a2:args) : bool =
    if List.length a1 = List.length a2
    then List.forall2 (fun a1 a2 -> match a1, a2 with
        | (Inl t, _), (Inl s, _) -> eq_typ t s
        | (Inr e, _), (Inr f, _) -> eq_exp e f
        | _ -> false) a1 a2
    else false
(* ------------------------------------------------ *)
(* <solver> The main solving algorithm              *)
(* ------------------------------------------------ *)
type flex_t = (typ * uvar_t * knd * args)
type im_or_proj_t = ((uvar_t * knd) * list<arg> * binders * ((list<ktec> -> typ) * (typ -> bool) * list<(option<binder> * variance * ktec)>))

let rigid_rigid       = 0
let flex_rigid_eq     = 1
let flex_refine_inner = 2
let flex_refine       = 3
let flex_rigid        = 4
let rigid_flex        = 5
let refine_flex       = 6
let flex_flex         = 7
let compress_prob wl p = match p with
    | KProb p -> {p with lhs=compress_k wl.tcenv wl p.lhs; rhs=compress_k wl.tcenv wl p.rhs} |> KProb
    | TProb p -> {p with lhs=compress   wl.tcenv wl p.lhs; rhs=compress   wl.tcenv wl p.rhs} |> TProb
    | EProb p -> {p with lhs=compress_e wl.tcenv wl p.lhs; rhs=compress_e wl.tcenv wl p.rhs} |> EProb
    | CProb _ -> p

let rank wl prob =
   let prob = compress_prob wl prob |> maybe_invert_p in
   match prob with
    | KProb kp ->
      let rank = begin match kp.lhs.n, kp.rhs.n with
        | Kind_uvar _, Kind_uvar _ -> flex_flex
        | Kind_uvar _, _ -> if kp.relation = EQ then flex_rigid_eq else flex_rigid
        | _, Kind_uvar _ -> if kp.relation = EQ then flex_rigid_eq else rigid_flex
        | _, _ -> rigid_rigid
        end in
      rank, {kp with rank=Some rank} |> KProb

    | TProb tp ->
      let lh, _ = Util.head_and_args tp.lhs in
      let rh, _ = Util.head_and_args tp.rhs in
      let rank, tp = begin match lh.n, rh.n with
        | Typ_uvar _, Typ_uvar _ -> flex_flex, tp

        | Typ_uvar _, _
        | _, Typ_uvar _ when (tp.relation=EQ) -> flex_rigid_eq, tp

        | Typ_uvar _, _ ->
          let b, ref_opt = base_and_refinement wl.tcenv wl tp.rhs in
          begin match ref_opt with
            | None -> flex_rigid, tp
            | _ ->
              let rank =
                if is_top_level_prob prob
                then flex_refine
                else flex_refine_inner in
              rank, {tp with rhs=force_refinement (b, ref_opt)}
          end

        | _, Typ_uvar _ ->
          let b, ref_opt = base_and_refinement wl.tcenv wl tp.lhs in
          begin match ref_opt with
            | None -> rigid_flex, tp
            | _ -> refine_flex, {tp with lhs=force_refinement (b, ref_opt)}
          end

        | _, _ -> rigid_rigid, tp
      end in
      rank, {tp with rank=Some rank} |> TProb

    | EProb ep ->
      let lh, _ = Util.head_and_args_e ep.lhs in
      let rh, _ = Util.head_and_args_e ep.rhs in
      let rank = match lh.n, rh.n with
        | Exp_uvar _, Exp_uvar _ -> flex_flex
        | Exp_uvar _, _
        | _, Exp_uvar _ -> flex_rigid_eq
        | _, _ -> rigid_rigid in
      rank, {ep with rank=Some rank} |> EProb

    | CProb cp -> rigid_rigid, {cp with rank=Some rigid_rigid} |> CProb

let next_prob wl =
//    match wl.attempting with
//        | hd::tl -> Some <| compress_prob wl hd, tl
//        | _ -> None, []
    let rec aux (min_rank, min, out) probs = match probs with
        | [] -> min, out, min_rank
        | hd::tl ->
          let rank, hd = rank wl hd in
          if rank <= flex_rigid_eq
          then match min with
            | None -> Some hd, out@tl, rank
            | Some m -> Some hd, out@m::tl, rank
          else if rank < min_rank
          then match min with
                | None -> aux (rank, Some hd, out) tl
                | Some m -> aux (rank, Some hd, m::out) tl
          else aux (min_rank, min, hd::out) tl in

   aux (flex_flex + 1, None, []) wl.attempting

let is_flex_rigid rank = flex_refine_inner <= rank && rank <= flex_rigid
let rec solve_flex_rigid_join env tp wl =
    if Tc.Env.debug env <| Options.Other "Rel"
    then Util.print1 "Trying to solve by joining refinements:%s\n" (prob_to_string env (TProb tp));
    let u, args = Util.head_and_args tp.lhs in
    let ok, head_match, partial_match, fallback, failed_match = 0,1,2,3,4 in
    let max i j = if i < j then j else i in

    let base_types_match t1 t2 : option<list<prob>> =
        let h1, args1 = Util.head_and_args t1 in
        let h2, _ = Util.head_and_args t2 in
        match h1.n, h2.n with
        | Typ_const tc1, Typ_const tc2 ->
          if lid_equals tc1.v tc2.v
          then (if List.length args1 = 0
                then Some []
                else Some [TProb <| new_problem env t1 EQ t2 None t1.pos "joining refinements"])
          else None

        | Typ_btvar a, Typ_btvar b ->
          if bvar_eq a b
          then Some []
          else None

        | _ -> None in

    let conjoin t1 t2 = match t1.n, t2.n with
        | Typ_refine(x, phi1), Typ_refine(y, phi2) ->
          let m = base_types_match x.sort y.sort in
          begin match m with
            | None -> None
            | Some m ->
               let phi2 = Util.subst_typ (Util.mk_subst_one_binder (Syntax.v_binder x) (Syntax.v_binder y)) phi2 in
               Some (mk_Typ_refine(x, Util.mk_conj phi1 phi2) (Some ktype) t1.pos, m)
          end

        | _, Typ_refine(y, _) ->
          let m = base_types_match t1 y.sort in
          begin match m with
            | None -> None
            | Some m -> Some (t2, m)
          end

        | Typ_refine(x, _), _ ->
          let m = base_types_match x.sort t2 in
          begin match m with
            | None -> None
            | Some m -> Some (t1, m)
          end

        | _ ->
          let m = base_types_match t1 t2 in
          begin match m with
            | None -> None
            | Some m -> Some (t1, m)
          end in

   let tt = u in//compress env wl u in
    match tt.n with
        | Typ_uvar(uv, _) ->
          //find all other constraints of the form uv <: t
          let upper_bounds, rest = wl.attempting |> List.partition (function
            | TProb tp ->
                begin match tp.rank with
                    | Some rank when is_flex_rigid rank ->
                      let u', _ = Util.head_and_args tp.lhs in
                      begin match (compress env wl u').n with
                        | Typ_uvar(uv', _) -> Unionfind.equivalent uv uv'
                        | _ -> false
                      end
                    | _ -> false // should be unreachable
                end
           | _ -> false) in

          let rec make_upper_bound (bound, sub_probs) tps = match tps with
            | [] -> Some (bound, sub_probs)
            | (TProb hd)::tl ->
              begin match conjoin bound (compress env wl hd.rhs) with
                    | Some(bound, sub) -> make_upper_bound (bound, sub@sub_probs) tl
                    | None -> None
              end
            | _ -> None in

          begin match make_upper_bound (compress env wl tp.rhs, []) upper_bounds with
            | None ->
              if Tc.Env.debug env <| Options.Other "Rel"
              then Util.print_string "No upper bounds\n";
              None

//            | Some rhs_bound, weak when (weak<>ok) ->
//              let eq_prob = new_problem env tp.lhs EQ rhs_bound None tp.loc "joining refinements" in
//              begin match solve_t env eq_prob ({wl with attempting=[]}) with
//                | Success (subst, _) ->
//                  Inl ({wl with subst=subst})
//                | _ -> Inr true
//              end

            | Some (rhs_bound, sub_probs) ->
              let eq_prob = new_problem env tp.lhs EQ rhs_bound None tp.loc "joining refinements" in
              match solve_t env eq_prob ({wl with attempting=sub_probs}) with
                | Success (subst, _) ->
                  let wl = {wl with attempting=rest; subst=[]} in
                  let wl = solve_prob (TProb tp) None subst wl in
                  let _ = List.fold_left (fun wl p -> solve_prob' true p None [] wl) wl upper_bounds in
                  Some wl
                | _ -> None
          end

      | _ -> failwith "Impossible: Not a flex-rigid"

and solve (env:Tc.Env.env) (probs:worklist) : solution =
//    printfn "Solving TODO:\n%s;;" (List.map prob_to_string probs.attempting |> String.concat "\n\t");
    match next_prob probs with
       | Some hd, tl, rank ->
         let probs = {probs with attempting=tl} in
         begin match hd with
            | KProb kp -> solve_k' env (maybe_invert kp) probs
            | TProb tp ->
              if not probs.defer_ok && flex_refine_inner <= rank && rank <= flex_rigid && not (!Options.no_slack)
              then begin match solve_flex_rigid_join env tp probs with
//                            | Inr true -> solve_t' env (maybe_invert tp) probs
                            | None -> solve_t' env (maybe_invert tp) probs//giveup env "join doesn't exist" hd
                            | Some wl -> solve env wl
                   end
              else solve_t' env (maybe_invert tp) probs
            | EProb ep -> solve_e' env (maybe_invert ep) probs
            | CProb cp -> solve_c env (maybe_invert cp) probs
         end
       | None, _, _ ->
         match probs.wl_deferred with
            | [] -> Success (probs.subst, {carry=[]; slack=probs.slack_vars}) //Yay ... done!
            | _ ->
              let attempt, rest = probs.wl_deferred |> List.partition (fun (c, _, _) -> c < probs.ctr) in
              match attempt with
                 | [] -> Success(probs.subst, {carry=List.map (fun (_, x, y) -> (x, y)) probs.wl_deferred; slack=probs.slack_vars})//can't solve yet; defer the rest
                 | _ -> solve env ({probs with attempting=attempt |> List.map (fun (_, _, y) -> y); wl_deferred=rest})


and solve_binders (env:Tc.Env.env) (bs1:binders) (bs2:binders) (orig:prob) (wl:worklist)
                  (rhs:binders -> Tc.Env.env -> list<subst_elt> -> prob) : solution =

   let rec aux scope env subst xs ys : either<(probs * formula), string> =
        match xs, ys with
            | [], [] ->
              let rhs_prob = rhs scope env subst in
              let formula = p_guard rhs_prob |> fst in
              Inl ([rhs_prob], formula)

            | (Inl _, _)::_, (Inr _, _)::_
            | (Inr _, _)::_, (Inl _, _)::_ -> Inr "sort mismatch"

            | hd1::xs, hd2::ys ->
               let subst = Util.mk_subst_one_binder hd2 hd1 @ subst in
               let env = Env.push_local_binding env (Env.binding_of_binder hd2) in
               let prob = match fst hd1, fst hd2 with
                 | Inl a, Inl b ->
                   KProb <| mk_problem (hd2::scope) orig (Util.subst_kind subst a.sort) (invert_rel <| p_rel orig) b.sort None "Formal type parameter"
                 | Inr x, Inr y ->
                   TProb <| mk_problem (hd2::scope) orig (Util.subst_typ subst x.sort)  (invert_rel <| p_rel orig) y.sort None "Formal value parameter"
                 | _ -> failwith "impos" in
               begin match aux (hd2::scope) env subst xs ys with
                 | Inr msg -> Inr msg
                 | Inl (sub_probs, phi) ->
                   let phi = Util.mk_conj (p_guard prob |> fst) (close_forall [hd2] phi) in
                   Inl (prob::sub_probs, phi)
               end

           | _ -> Inr "arity mismatch" in

   let scope = Env.binders env in
   match aux scope env [] bs1 bs2 with
    | Inr msg -> giveup env msg orig
    | Inl (sub_probs, phi) ->
      let wl = solve_prob orig (Some phi) [] wl in
      solve env (attempt sub_probs wl)

and solve_k env problem wl =
    match compress_prob wl (KProb problem) with
        | KProb p -> solve_k' env p wl
        | _ -> failwith "impossible"

and solve_k' (env:Env.env) (problem:problem<knd,unit>) (wl:worklist) : solution =
    let orig = KProb problem in
    if Util.physical_equality problem.lhs problem.rhs then solve env (solve_prob orig None [] wl) else
    let k1 = problem.lhs in
    let k2 = problem.rhs in
    if Util.physical_equality k1 k2 then solve env (solve_prob orig None [] wl) else
    let r = Env.get_range env in

    let imitate_k (rel, u, ps, xs, (h, qs)) =
        //U p1..pn =?= h q1..qm
        //extend_subst: (U -> \x1..xn. h (G1(x1..xn), ..., Gm(x1..xm)))
        //sub-problems: Gi(p1..pn) =?= qi
        let r = Env.get_range env in
        let sub_probs, gs_xs, f = imitation_sub_probs orig env xs ps qs in
        let im = mk_Kind_lam(xs, h gs_xs) r in
        let wl = solve_prob orig (Some f) [UK(u, im)] wl in
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
                 solve env (solve_prob orig None [UK(u, k1)] wl)
            else imitate_k (rel, u, xs |> Util.args_of_non_null_binders, xs, decompose_kind env k)

          | None ->
            giveup env ("flex-rigid: not a pattern") (KProb problem) in

    match k1.n, k2.n with
     | Kind_type, Kind_type
     | Kind_effect, Kind_effect -> solve env <| solve_prob orig None [] wl

     | Kind_abbrev(_, k1), _ -> solve_k env ({problem with lhs=k1}) wl
     | _, Kind_abbrev(_, k2) -> solve_k env ({problem with rhs=k2}) wl

     | Kind_arrow(bs1, k1'), Kind_arrow(bs2, k2') ->
       let sub_prob scope env subst =
           KProb <| mk_problem scope orig (Util.subst_kind subst k1') problem.relation k2' None "Arrow-kind result"  in
       solve_binders env bs1 bs2 orig wl sub_prob

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
                  let wl = solve_prob orig None [UK(u1, k1); UK(u2, k2)] wl in
                  solve env wl
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
    let p = compress_prob wl (TProb problem) in
    match p with
        | TProb p -> solve_t' env p wl
        | _ -> failwith "Impossible"

and solve_t' (env:Env.env) (problem:problem<typ,exp>) (wl:worklist) : solution =
    let giveup_or_defer orig msg =
        if wl.defer_ok
        then begin
            if Tc.Env.debug env <| Options.Other "Rel"
            then Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" (prob_to_string env orig) msg;
            solve env (defer msg orig wl)
        end
        else giveup env msg orig in

    (* <imitate_t> used in flex-rigid *)
    let imitate_t orig (env:Tc.Env.env) (wl:worklist) (p:im_or_proj_t) : solution =
        let ((u,k), ps, xs, (h, _, qs)) = p in
        let xs = sn_binders env xs in
        //U p1..pn REL h q1..qm
        //if h is not a free variable
        //extend_subst: (U -> \x1..xn. h (G1(x1..xn), ..., Gm(x1..xm)))
        //sub-problems: Gi(p1..pn) REL' qi, where REL' = vary_rel REL (variance h i)
        let r = Env.get_range env in
        let sub_probs, gs_xs, formula = imitation_sub_probs orig env xs ps qs in
        let im = mk_Typ_lam'(xs, h gs_xs) None r in
        if Tc.Env.debug env <| Options.Other "Rel"
        then Util.print4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n"
            (Print.typ_to_string im) (Print.tag_of_typ im)
            (List.map (prob_to_string env) sub_probs |> String.concat ", ")
            (Normalize.formula_norm_to_string env formula);
        let wl = solve_prob orig (Some formula) [UT((u,k), im)] wl in
        solve env (attempt sub_probs wl) in
    (* </imitate_t> *)

    (* <project_t> used in flex_rigid *)
    let project_t orig (env:Tc.Env.env) (wl:worklist) (i:int) (p:im_or_proj_t) : option<solution> =
        let (u, ps, xs, (h, matches, qs)) = p in
        //U p1..pn REL h q1..qm
        //extend subst: U -> \x1..xn. xi(G1(x1...xn) ... Gk(x1..xm)) ... where k is the arity of ti
        //sub-problems: pi(G1(p1..pn)..Gk(p1..pn)) REL h q1..qm
        let r = Env.get_range env in
        let pi = List.nth ps i in
        let rec gs k =
            let bs, k = Util.kind_formals k in
            let rec aux subst bs = match bs with
                | [] -> [], []
                | hd::tl ->
                    let gi_xs, gi_ps, subst = match fst hd with
                        | Inl a ->
                            let k_a = Util.subst_kind subst a.sort in
                            let gi_xs, gi = new_tvar r xs k_a in
                            let gi_xs = Tc.Normalize.eta_expand env gi_xs in
                            let gi_ps = mk_Typ_app(gi, ps) (Some k_a) r in
                            let subst = if is_null_binder hd then subst else Inl(a.v, gi_xs)::subst in
                            targ gi_xs, targ gi_ps, subst

                        | Inr x ->
                            let t_x = Util.subst_typ subst x.sort in
                            let gi_xs, gi = new_evar r xs t_x in
                            let gi_xs = Tc.Normalize.eta_expand_exp env gi_xs in
                            let gi_ps = mk_Exp_app(gi, ps) (Some t_x) r in
                            let subst = if is_null_binder hd then subst else Inr(x.v, gi_xs)::subst in
                            varg gi_xs, varg gi_ps, subst in
                    let gi_xs', gi_ps' = aux subst tl in
                    gi_xs::gi_xs', gi_ps::gi_ps' in
              aux [] bs in

        match fst pi, fst <| List.nth xs i with
            | Inl pi, Inl xi ->
                if not <| matches pi
                then None
                else let g_xs, _ = gs xi.sort in
                     let xi = btvar_to_typ xi in
                     let proj = mk_Typ_lam(xs, mk_Typ_app'(xi, g_xs) (Some ktype) r) None r in
                     let sub =
                        TProb <| mk_problem (p_scope orig) orig (mk_Typ_app'(proj, ps) (Some ktype) r) (p_rel orig) (h <| List.map (fun (_, _, y) -> y) qs) None "projection" in
                     if debug env <| Options.Other "Rel" then Util.print2 "Projecting %s\n\tsubprob=%s\n" (Print.typ_to_string proj) (prob_to_string env sub);
                     let wl = solve_prob orig (Some (fst <| p_guard sub)) [UT(u, proj)] wl in
                     Some <| solve env (attempt [sub] wl)
            | _ -> None in
    (* </project_t> *)

    (* <flex-rigid> *)
    let solve_t_flex_rigid orig (lhs:(flex_t * option<binders>)) (t2:typ) (wl:worklist) =
        let (t1, uv, k, args_lhs), maybe_pat_vars = lhs in
        let subterms ps =
            let xs = Util.kind_formals k |> fst in
            let xs = Util.name_binders xs in
            (uv,k), ps, xs, decompose_typ env t2 in

        let rec imitate_or_project n st i =
            if i >= n then giveup env "flex-rigid case failed all backtracking attempts" orig
            else if i = -1
            then match imitate_t orig env wl st with
                    | Failed _ -> imitate_or_project n st (i + 1) //backtracking point
                    | sol -> sol
            else match project_t orig env wl i st with
                    | None
                    | Some (Failed _) -> imitate_or_project n st (i + 1) //backtracking point
                    | Some sol -> sol in

        let check_head fvs1 t2 =
            let hd, _ = Util.head_and_args t2 in
            match hd.n with
                | Typ_fun _
                | Typ_const _
                | Typ_lam _  -> true
                | _ ->
                    let fvs_hd = Util.freevars_typ hd in
                    if Util.fvs_included fvs_hd fvs1
                    then true
                    else (if Tc.Env.debug env <| Options.Other "Rel" then Util.print1 "Free variables are %s" (Print.freevars_to_string fvs_hd); false) in

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
                let occurs_ok, msg = occurs_check env wl (uv,k) t2 in
                if not occurs_ok
                then giveup_or_defer orig ("occurs-check failed: " ^ (Option.get msg))
                else if Util.fvs_included fvs2 fvs1
                then (if Util.is_function_typ t2 && p_rel orig <> EQ //function types have structural subtyping and have to be imitated
                      then imitate_t orig env wl (subterms args_lhs)
                      else //fast solution, pattern equality
                           let _  = if debug env <| Options.Other "Rel"
                                    then Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" (Print.typ_to_string t1) (Print.freevars_to_string fvs1) (Print.freevars_to_string fvs2) in
                           let sol = match vars with
                                | [] -> t2
                                | _ -> mk_Typ_lam(sn_binders env vars, t2) None t1.pos in
                           let wl = solve_prob orig None [UT((uv,k), sol)] wl in
                           solve env wl)
                else if wl.defer_ok
                then solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl)
                else if check_head fvs1 t2
                then let _ = if debug env <| Options.Other "Rel"
                             then Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                               (Print.typ_to_string t1) (Print.freevars_to_string fvs1)
                                               (Print.freevars_to_string fvs2) in
                     imitate_or_project (List.length args_lhs) (subterms args_lhs) (-1)
                else giveup env "free-variable check failed on a non-redex" orig

          | None ->
                if wl.defer_ok
                then solve env (defer "not a pattern" orig wl)
                else if check_head (Util.freevars_typ t1) t2
                then let im_ok = imitate_ok t2 in
                     let _ = if debug env <| Options.Other "Rel"
                             then Util.print2 "Not a pattern (%s) ... %s\n" (Print.typ_to_string t1) (if im_ok < 0 then "imitating" else "projecting") in
                     imitate_or_project (List.length args_lhs) (subterms args_lhs) im_ok
                else giveup env "head-symbol is free" orig in
   (* </flex-rigid> *)

   (* <flex-flex>:
      Always delay flex-flex constraints, if possible.
      Then, if it delaying is not an option, interpret a flex-flex constraint as an equality, even if it is tagged as SUB/SUBINV
      This may cause a loss of generality. Consider:

        nat <: u1 <: u2
               int <: u2
               u1 <: nat

      By collapsing u1 and u2, the constraints become unsolveable, since we then have
        nat <: u <: nat and int <: u

      However, it seems unlikely that this would arise in practice,
      since all the other non-flex-flex constraints would be attempted first.

      The alternative is to delay all flex-flex subtyping constraints, even the pattern cases.
      But, it seems that performance would suffer greatly then. TBD.
   *)
   let flex_flex orig (lhs:flex_t) (rhs:flex_t) : solution =
        if wl.defer_ok && p_rel orig <> EQ then solve env (defer "flex-flex deferred" orig wl) else

        let force_quasi_pattern xs_opt (t, u, k, args) =
            let rec aux binders ys args = match args with
                | [] ->
                    let ys = List.rev ys in
                    let binders = List.rev binders in
                    let kk = Recheck.recompute_kind t in
                    let t', _ = new_tvar t.pos ys kk in
                    let u1_ys, u1, k1, _ = destruct_flex_t t' in
                    let sol = UT((u,k), mk_Typ_lam(binders, u1_ys) (Some k) t.pos) in
                    sol, (t', u, k1, ys)

                | hd::tl ->
                  let new_binder hd = match fst hd with
                        | Inl a -> Recheck.recompute_kind a |> Util.gen_bvar_p a.pos |> Syntax.t_binder
                        | Inr x -> Recheck.recompute_typ  x |> Util.gen_bvar_p x.pos |> Syntax.v_binder in

                  let binder, ys = match pat_var_opt env ys hd with
                    | None -> new_binder hd, ys

                    | Some y ->
                      begin match xs_opt with
                        | None -> y, y::ys
                        | Some xs ->
                          if xs |> Util.for_some (Util.eq_binder y)
                          then y, y::ys  //this is a variable in the intersection with xs
                          else new_binder hd, ys
                      end in


                    aux (binder::binders) ys tl in

           aux [] [] args in


        let solve_both_pats wl (u1, k1, xs) (u2, k2, ys) k r =
            if Unionfind.equivalent u1 u2 && binders_eq xs ys
            then solve env (solve_prob orig None [] wl)
            else //U1 xs =?= U2 ys
                 //zs = xs intersect ys, U fresh
                 //U1 = \x1 x2. U zs
                 //U2 = \y1 y2 y3. U zs
                let xs = sn_binders env xs in
                let ys = sn_binders env ys in
                let zs = intersect_vars xs ys in
                let u_zs, _ = new_tvar r zs k in
                let sub1 = mk_Typ_lam'(xs, u_zs) (Some k1) r in
                let occurs_ok, msg = occurs_check env wl (u1,k1) sub1 in
                if not occurs_ok
                then giveup_or_defer orig "flex-flex: failed occcurs check"
                else let sol1 = UT((u1, k1), sub1) in
                        if Unionfind.equivalent u1 u2
                        then let wl = solve_prob orig None [sol1] wl in
                                solve env wl
                        else let sub2 = mk_Typ_lam'(ys, u_zs) (Some k2) r in
                                let occurs_ok, msg = occurs_check env wl (u2,k2) sub2 in
                                if not occurs_ok
                                then giveup_or_defer orig "flex-flex: failed occurs check"
                                else let sol2 = UT((u2,k2), sub2) in
                                    let wl = solve_prob orig None [sol1;sol2] wl in
                                    solve env wl in

        let solve_one_pat (t1, u1, k1, xs) (t2, u2, k2, args2) =
            begin
                if Tc.Env.debug env <| Options.Other "Rel"
                then Util.print2 "Trying flex-flex one pattern (%s) with %s\n" (Print.typ_to_string t1) (Print.typ_to_string t2);
                if Unionfind.equivalent u1 u2
                then let sub_probs = List.map2 (fun a b ->
                               let a = Util.arg_of_non_null_binder a in
                               match fst a, fst b with
                                | Inl t1, Inl t2 -> mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index" |> TProb
                                | Inr t1, Inr t2 -> mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index" |> EProb
                                | _ -> failwith "Impossible") xs args2 in
                     let guard = Util.mk_conj_l (List.map (fun p -> p_guard p |> fst) sub_probs) in
                     let wl = solve_prob orig (Some guard) [] wl in
                     solve env (attempt sub_probs wl)
                else
                     let t2 = sn env t2 in
                     let rhs_vars = Util.freevars_typ t2 in
                     let occurs_ok, _ = occurs_check env wl (u1,k1) t2 in
                     let lhs_vars = freevars_of_binders xs in
                     if occurs_ok && Util.fvs_included rhs_vars lhs_vars
                     then let sol = UT((u1, k1), mk_Typ_lam'(xs, t2) (Some k1) t1.pos) in
                          let wl = solve_prob orig None [sol] wl in
                          solve env wl
                     else if occurs_ok && not <| wl.defer_ok
                     then let sol, (_, u2, k2, ys) = force_quasi_pattern (Some xs) (t2, u2, k2, args2) in
                          let wl = extend_solution sol wl in
                          let _ = if Tc.Env.debug env <| Options.Other "QuasiPattern" then Util.print1 "flex-flex quasi pattern (2): %s\n" (uvi_to_string env sol) in
                          match orig with
                            | TProb p -> solve_t env p wl
                            | _ -> giveup env "impossible" orig
                     else giveup_or_defer orig "flex-flex constraint"
            end in

        let (t1, u1, k1, args1) = lhs in
        let (t2, u2, k2, args2) = rhs in
        let maybe_pat_vars1 = pat_vars env [] args1 in
        let maybe_pat_vars2 = pat_vars env [] args2 in
        let r = t2.pos in
        match maybe_pat_vars1, maybe_pat_vars2 with
            | Some xs, Some ys -> solve_both_pats wl (u1, k1, xs) (u2, k2, ys) (Recheck.recompute_kind t2) t2.pos
            | Some xs, None -> solve_one_pat (t1, u1, k1, xs) rhs
            | None, Some ys -> solve_one_pat (t2, u2, k2, ys) lhs
            | _ ->
              if wl.defer_ok
              then giveup_or_defer orig "flex-flex: neither side is a pattern"
              else let sol, _ = force_quasi_pattern None (t1, u1, k1, args1) in
                   let wl = extend_solution sol wl in
                   let _ = if Tc.Env.debug env <| Options.Other "QuasiPattern" then Util.print1 "flex-flex quasi pattern (1): %s\n" (uvi_to_string env sol) in
                   match orig with
                    | TProb p -> solve_t env p wl
                    | _ -> giveup env "impossible" orig  in
    (* </flex-flex> *)

    let orig = TProb problem in
    if Util.physical_equality problem.lhs problem.rhs then solve env (solve_prob orig None [] wl) else
    let t1 = problem.lhs in
    let t2 = problem.rhs in
    if Util.physical_equality t1 t2 then solve env (solve_prob orig None [] wl) else
    let _ =
        if debug env (Options.Other "Rel")
        then Util.print2 "Attempting %s\n\tSubst is %s\n" (prob_to_string env orig) (List.map (uvi_to_string wl.tcenv) wl.subst |> String.concat "; ") in
    let r = Env.get_range env in

    let match_num_binders : (list<'a> * (list<'a> -> 'b)) -> (list<'a> * (list<'a> -> 'b)) -> (list<'a> * 'b) * (list<'a> * 'b) =
        fun (bs1, mk_cod1) (bs2, mk_cod2) ->
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
        then solve env (solve_prob orig None [] wl)
        else solve env (solve_prob orig (Some <| Util.mk_eq_typ t1 t2) [] wl)

      | Typ_fun(bs1, c1), Typ_fun(bs2, c2) ->
        let mk_c c = function
            | [] -> c
            | bs -> mk_Total(mk_Typ_fun(bs, c) None c.pos) in
        let (bs1, c1), (bs2, c2) =
            match_num_binders (bs1, mk_c c1) (bs2, mk_c c2) in
        solve_binders env bs1 bs2 orig wl
        (fun scope env subst  ->
            let c1 = Util.subst_comp subst c1 in
            let rel = if !Options.use_eq_at_higher_order then EQ else problem.relation in
            let _ = if Tc.Env.debug env <| Options.Other "EQ"
                    then Util.print2 "(%s) Using relation %s at higher order\n" (Env.get_range env |> Range.string_of_range) (rel_to_string rel) in
            CProb <| mk_problem scope orig c1 rel c2 None "function co-domain")

      | Typ_lam(bs1, t1'), Typ_lam(bs2, t2') ->
        let mk_t t = function
            | [] -> t
            | bs -> mk_Typ_lam(bs, t) None t.pos in
        let (bs1, t1'), (bs2, t2') =
            match_num_binders (bs1, mk_t t1') (bs2, mk_t t2') in
        solve_binders env bs1 bs2 orig wl
        (fun scope env subst ->
            let t1' = Util.subst_typ subst t1' in
            TProb <| mk_problem scope orig t1' problem.relation t2' None "lambda co-domain")

      | Typ_refine _, Typ_refine _ ->
        let x1, phi1 = as_refinement env wl t1 in
        let x2, phi2 = as_refinement env wl t2 in
        let base_prob = TProb <| mk_problem (p_scope orig) orig x1.sort problem.relation x2.sort problem.element "refinement base type" in
        let x1_for_x2 = Util.mk_subst_one_binder (v_binder x1) (v_binder x2) in
        let phi2 = Util.subst_typ x1_for_x2 phi2 in
        let mk_imp imp phi1 phi2 = imp phi1 phi2 |> guard_on_element problem x1 in
        let fallback () =
            let impl =
                if problem.relation = EQ
                then mk_imp Util.mk_iff phi1 phi2
                else mk_imp Util.mk_imp phi1 phi2 in
            let guard = Util.mk_conj (p_guard base_prob |> fst) impl in
            let wl = solve_prob orig (Some guard) [] wl in
            solve env (attempt [base_prob] wl) in
        if problem.relation = EQ
        then let ref_prob = TProb <| mk_problem (p_scope orig) orig phi1 EQ phi2 None "refinement formula" in
             begin match solve env ({wl with defer_ok=false; attempting=[ref_prob]; wl_deferred=[]}) with
                    | Failed _ -> fallback()
                    | Success (subst, _) ->
//                      if Tc.Env.debug env <| Options.Other "RefEq"
//                      then Util.fprint1 "Got guard %s\n" (Normalize.formula_norm_to_string env <| (fst <| p_guard ref_prob));
                      let guard = Util.mk_conj (p_guard base_prob |> fst) (p_guard ref_prob |> fst |> guard_on_element problem x1) in
                      let wl = solve_prob orig (Some guard) [] wl in
                      let wl = {wl with subst=subst; ctr=wl.ctr+1} in
                      solve env (attempt [base_prob] wl)
             end
        else fallback()

      (* flex-flex *)
      | Typ_uvar _,                 Typ_uvar _
      | Typ_app({n=Typ_uvar _}, _), Typ_uvar _
      | Typ_uvar _,                 Typ_app({n=Typ_uvar _}, _)
      | Typ_app({n=Typ_uvar _}, _), Typ_app({n=Typ_uvar _}, _) ->
        flex_flex orig (destruct_flex_t t1) (destruct_flex_t t2)

      (* flex-rigid equalities *)
      | Typ_uvar _, _
      | Typ_app({n=Typ_uvar _}, _), _ when (problem.relation=EQ) -> (* just imitate/project ... no slack *)
        solve_t_flex_rigid orig (destruct_flex_pattern env t1) t2 wl

      (* rigid-flex: reorient if it is an equality constraint *)
      | _, Typ_uvar _
      | _, Typ_app({n=Typ_uvar _}, _) when (problem.relation = EQ) ->
        solve_t env (invert problem) wl

      (* flex-rigid: subtyping *)
      | Typ_uvar _, _
      | Typ_app({n=Typ_uvar _}, _), _ -> (* equate with the base type of the refinement on the RHS, and add a logical guard for the refinement formula *)
        if wl.defer_ok
        then solve env (defer "flex-rigid subtyping deferred" orig wl)
        else
            let new_rel = if !Options.no_slack then EQ else problem.relation in
            if not <| is_top_level_prob orig //If it's not top-level and t2 is refined, then we should not try to prove that t2's refinement is saturated
            then solve_t_flex_rigid (TProb <| {problem with relation=new_rel}) (destruct_flex_pattern env t1) t2 wl
            else let t_base, ref_opt = base_and_refinement env wl t2 in
                 begin match ref_opt with
                        | None -> //no useful refinement on the RHS, so just equate and solve
                          solve_t_flex_rigid (TProb <| {problem with relation=new_rel}) (destruct_flex_pattern env t1) t_base wl

                        | Some (y, phi) ->
                          let y' = {y with sort = t1} in
                          let impl = guard_on_element problem y' phi in
                          let base_prob =
                            TProb <| mk_problem problem.scope orig t1 new_rel y.sort problem.element "flex-rigid: base type" in
                          let guard = Util.mk_conj (p_guard base_prob |> fst) impl in
                          let wl = solve_prob orig (Some guard) [] wl in
                          solve env (attempt [base_prob] wl)
                 end

      (* rigid-flex: subtyping *)
      | _, Typ_uvar _
      | _, Typ_app({n=Typ_uvar _}, _) -> (* widen immediately, by forgetting the top-level refinement and equating *)
        if wl.defer_ok
        then solve env (defer "rigid-flex subtyping deferred" orig wl)
        else let t_base, _ = base_and_refinement env wl t1 in
             solve_t env ({problem with lhs=t_base; relation=EQ}) wl

      | Typ_refine _, _ ->
        let t2 = force_refinement <| base_and_refinement env wl t2 in
        solve_t env ({problem with rhs=t2}) wl

      | _, Typ_refine _ ->
        let t1 = force_refinement <| base_and_refinement env wl t1 in
        solve_t env ({problem with lhs=t1}) wl

      | Typ_btvar _, _
      | Typ_const _, _
      | Typ_app _, _
      | _, Typ_btvar _
      | _, Typ_const _
      | _, Typ_app _ ->
         let m, o = head_matches_delta env wl t1 t2 in
         begin match m, o  with
            | (MisMatch, _) -> //heads definitely do not match
              let head1 = Util.head_and_args t1 |> fst in
              let head2 = Util.head_and_args t2 |> fst in
              let may_equate head = match head.n with
                | Typ_btvar _  -> true
                | Typ_const tc -> Env.is_projector env tc.v
                | _ -> false  in
              if (may_equate head1 || may_equate head2) && wl.smt_ok
              then solve env (solve_prob orig (Some <| Util.mk_eq_typ t1 t2) [] wl)
              else giveup env "head mismatch" orig


            | (_, Some (t1, t2)) -> //heads match after some delta steps
              solve_t env ({problem with lhs=t1; rhs=t2}) wl

            | (_, None) -> //head matches head'
                if debug env <| Options.Other "Rel" then Util.print2 "Head matches: %s and %s\n" (Print.typ_to_string t1) (Print.typ_to_string t2);
                let head, args = Util.head_and_args t1 in
                let head', args' = Util.head_and_args t2 in
                let nargs = List.length args in
                if nargs <> List.length args'
                then giveup env (Util.format4 "unequal number of arguments: %s[%s] and %s[%s]"
                            (Print.typ_to_string head)
                            (Print.args_to_string args)
                            (Print.typ_to_string head')
                            (Print.args_to_string args'))
                            orig
                else if nargs=0 || eq_args args args'
                then solve env (solve_prob orig None [] wl)  //special case works well for easily proving things like nat <: nat, or greater_than i <: greater_than i etc.
                else //Given T t1 ..tn REL T s1..sn
                     //  if T expands to a refinement, then normalize it and recurse
                     //  This allows us to prove things like
                     //         type T (x:int) (y:int) = z:int{z = x + y}
                     //         T 0 1 <: T 1 0
                     //  By expanding out the definitions
                     //
                     //Otherwise, we reason extensionally about T and try to solve ti = si, for all i
                     let base1, refinement1 = base_and_refinement env wl t1 in
                     let base2, refinement2 = base_and_refinement env wl t2 in
                     begin match refinement1, refinement2 with
                             | None, None ->  //neither side is a refinement; reason extensionally
                               let _ = if head_matches head head <> FullMatch
                                       then failwith (Util.format2 "Assertion failed: expected full match of %s and %s\n" (Print.typ_to_string head) (Print.typ_to_string head')) in
                               let subprobs = List.map2 (fun a a' -> match fst a, fst a' with
                                    | Inl t, Inl t' ->
                                      TProb <| mk_problem (p_scope orig) orig t EQ t' None "type index"
                                    | Inr v, Inr v' ->
                                      EProb <| mk_problem (p_scope orig) orig v EQ v' None "term index"
                                    | _ -> failwith "Impossible" (*terms are well-kinded*)) args args' in
                               let formula = Util.mk_conj_l (List.map (fun p -> fst (p_guard p)) subprobs) in
                               let wl = solve_prob orig (Some formula) [] wl in
                               solve env (attempt subprobs wl)

                              | _ ->
                               let lhs = force_refinement (base1, refinement1) in
                               let rhs = force_refinement (base2, refinement2) in
                               solve_t env ({problem with lhs=lhs; rhs=rhs}) wl
                    end
          end

      | Typ_ascribed _ , _
      | Typ_meta _, _
      | Typ_delayed _, _
      | _, Typ_ascribed _
      | _, Typ_meta _
      | _, Typ_delayed _ -> failwith "Impossible"

      | _ -> giveup env "head mismatch" orig

and solve_c (env:Env.env) (problem:problem<comp,unit>) (wl:worklist) : solution =
    let c1 = problem.lhs in
    let c2 = problem.rhs in
    let orig = CProb problem in
    let sub_prob : 'a -> rel -> 'a -> string -> problem_t<'a,'b> =
        fun t1 rel t2 reason -> mk_problem (p_scope orig) orig t1 rel t2 None reason in
    let solve_eq c1_comp c2_comp =
        let _ = if Tc.Env.debug env <| Options.Other "EQ"
                then Util.print_string "solve_c is using an equality constraint\n" in
        let sub_probs = List.map2 (fun arg1 arg2 -> match fst arg1, fst arg2 with
            | Inl t1, Inl t2 -> TProb<| sub_prob t1 EQ t2 "effect arg"
            | Inr e1, Inr e2 -> EProb<| sub_prob e1 EQ e2 "effect arg"
            | _ -> failwith "impossible") c1_comp.effect_args c2_comp.effect_args in
        let guard = Util.mk_conj_l (List.map (fun p -> p_guard p |> fst) sub_probs) in
        let wl = solve_prob orig (Some guard) [] wl in
        solve env (attempt sub_probs wl) in
    if Util.physical_equality c1 c2
    then solve env (solve_prob orig None [] wl)
    else let _ = if debug env <| Options.Other "Rel" then Util.print3 "solve_c %s %s %s\n" (Print.comp_typ_to_string c1) (rel_to_string problem.relation) (Print.comp_typ_to_string c2) in
         let r = Env.get_range env in
         let c1_0, c2_0 = c1, c2 in
         match c1.n, c2.n with
               | Total t1, Total t2 -> //rigid-rigid 1
                 solve_t env (problem_using_guard orig t1 problem.relation t2 None "result type") wl

               | Total _,  Comp _ ->
                 solve_c env ({problem with lhs=mk_Comp <| comp_to_comp_typ c1}) wl
               | Comp _, Total _ ->
                 solve_c env ({problem with rhs=mk_Comp <| comp_to_comp_typ c2}) wl

               | Comp _, Comp _ ->
                 if (Util.is_ml_comp c1 && Util.is_ml_comp c2)
                    || (Util.is_total_comp c1 && (Util.is_total_comp c2 || Util.is_ml_comp c2))
                 then solve_t env (problem_using_guard orig (Util.comp_result c1) problem.relation (Util.comp_result c2) None "result type") wl
                 else let c1_comp = Util.comp_to_comp_typ c1 in
                      let c2_comp = Util.comp_to_comp_typ c2 in
                      if problem.relation=EQ && lid_equals c1_comp.effect_name c2_comp.effect_name
                      then solve_eq c1_comp c2_comp
                      else
                         let c1 = Normalize.weak_norm_comp env c1 in
                         let c2 = Normalize.weak_norm_comp env c2 in
                         if debug env <| Options.Other "Rel" then Util.print2 "solve_c for %s and %s\n" (c1.effect_name.str) (c2.effect_name.str);
                         begin match Tc.Env.monad_leq env c1.effect_name c2.effect_name with
                           | None -> giveup env (Util.format2 "incompatible monad ordering: %s </: %s" (Print.sli c1.effect_name) (Print.sli c2.effect_name)) orig
                           | Some edge ->
                             if problem.relation = EQ
                             then let wp, wlp = match c1.effect_args with
                                                   | [(Inl wp1,_); (Inl wlp1, _)] -> wp1, wlp1
                                                   | _ -> failwith (Util.format1 "Unexpected number of indices on a normalized effect (%s)" (Range.string_of_range (Syntax.range_of_lid c1.effect_name))) in
                                  let c1 = {
                                    effect_name=c2.effect_name;
                                    result_typ=c1.result_typ;
                                    effect_args=[targ (edge.mlift c1.result_typ wp); targ (edge.mlift c1.result_typ wlp)];
                                    flags=c1.flags
                                  } in
                                  solve_eq c1 c2
                             else let is_null_wp_2 = c2.flags |> Util.for_some (function TOTAL | MLEFFECT | SOMETRIVIAL -> true | _ -> false) in
                                  let wpc1, wpc2 = match c1.effect_args, c2.effect_args with
                                    | (Inl wp1, _)::_, (Inl wp2, _)::_ -> wp1, wp2
                                    | _ -> failwith (Util.format2 "Got effects %s and %s, expected normalized effects" (Print.sli c1.effect_name) (Print.sli c2.effect_name)) in
                                  if Util.physical_equality wpc1 wpc2
                                  then solve_t env (problem_using_guard orig c1.result_typ problem.relation c2.result_typ None "result type") wl
                                  else let c2_decl = Tc.Env.get_effect_decl env c2.effect_name in
                                       let g =
                                       if is_null_wp_2
                                       then let _ = if debug env <| Options.Other "Rel" then Util.print_string "Using trivial wp ... \n" in
                                            mk_Typ_app(c2_decl.trivial, [targ c1.result_typ; targ <| edge.mlift c1.result_typ wpc1]) (Some ktype) r
                                       else let wp2_imp_wp1 = mk_Typ_app(c2_decl.wp_binop,
                                                                            [targ c2.result_typ;
                                                                            targ wpc2;
                                                                            targ <| Util.ftv Const.imp_lid (Const.kbin ktype ktype ktype);
                                                                            targ <| edge.mlift c1.result_typ wpc1]) None r in
                                                mk_Typ_app(c2_decl.wp_as_type, [targ c2.result_typ; targ wp2_imp_wp1]) (Some ktype) r  in
                                       let base_prob = TProb <| sub_prob c1.result_typ problem.relation c2.result_typ "result type" in
                                       let wl = solve_prob orig (Some <| Util.mk_conj (p_guard base_prob |> fst) g) [] wl in
                                       solve env (attempt [base_prob] wl)
                         end

and solve_e env problem wl =
    match compress_prob wl (EProb problem) with
        | EProb p -> solve_e' env p wl
        | _ -> failwith "Impossible"

and solve_e' (env:Env.env) (problem:problem<exp,unit>) (wl:worklist) : solution =
    let problem = {problem with relation=EQ} in //expression problems are always equalities
    let e1 = problem.lhs in
    let e2 = problem.rhs in
    let orig = EProb problem in
    let sub_prob : 'a -> 'a -> string -> problem_t<'a,'b> =
        fun lhs rhs reason -> mk_problem (p_scope orig) orig lhs EQ rhs None reason in
    let _ = if debug env <| Options.Other "Rel" then Util.print1 "Attempting:\n%s\n" (prob_to_string env orig) in

    let flex_rigid (e1, u1, t1, args1) e2 =
        //u arg1...argn =?= e2
        let maybe_vars1 = pat_vars env [] args1 in

        let sub_problems xs args2 =
            let gi_xi, gi_pi = args2 |> List.map (function
            | Inl t, imp ->
                let kk = Recheck.recompute_kind t in
                let gi_xi, gi = new_tvar t.pos xs kk in
                let gi_pi = mk_Typ_app'(gi, args1) (Some kk) t.pos in
                (Inl gi_xi, imp), TProb <| sub_prob gi_pi t "type index"
            | Inr v, imp ->
                let tt = Recheck.recompute_typ v in
                let gi_xi, gi = new_evar v.pos xs tt in
                let gi_pi = mk_Exp_app'(gi, args1) (Some tt) v.pos in
                (Inr gi_xi, imp), EProb <| sub_prob gi_pi v "expression index") |> List.unzip in
        let formula = Util.mk_conj_l (List.map (fun p -> p_guard p |> fst) gi_pi) in
        gi_xi, gi_pi, formula in

        let project_e head2 args2 =
            //u p1..pn =?= y a1 .. am
            //if pi = y
            //u = \x1..xn. xi (G1 (x1..xn), ..., Gm (x1..xn))
            //Gi(p1..pn) =?= ai
            let giveup reason = giveup env (Util.format1 "flex-rigid: refusing to project expressions (%s)" reason) orig in
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
                                          then let gi_xi, gi_pi, f = sub_problems all_xs args2 in
                                               let sol = mk_Exp_abs(all_xs, mk_Exp_app'(Util.bvar_to_exp xi, gi_xi) None e1.pos) None e1.pos in
                                               if Tc.Env.debug env <| Options.Other "Rel"
                                               then Util.print3 "Projected: %s -> %s\nSubprobs=\n%s\n" (Print.uvar_e_to_string (u1,t1)) (Print.exp_to_string sol) (gi_pi |> List.map (prob_to_string env) |> String.concat "\n");
                                               solve env (attempt gi_pi (solve_prob orig (Some f) [UE((u1, t1), sol)] wl))
                                          else aux xs args
                                       | _ -> aux xs args
                                end
                            | x::xs, arg::args -> giveup (Util.format2 "type incorrect term---impossible: expected %s; got %s\n" (Print.binder_to_string x) (Print.arg_to_string arg)) in
                          aux (List.rev all_xs) (List.rev args1)

                | _ -> giveup "rigid head term is not a variable"  in

        let imitate_or_project_e () =
            if wl.defer_ok
            then solve env (defer "flex-rigid: not a pattern" orig wl)
            else
                //u1 p1..pn =?= h a1..am
                //if h not occurs in u1 and h not free
                //u1 = \x1..xn. h (G1(x1...xn), ..., Gm(x1..xn))
                //and Gi(p1..pn) =?= ai
                let _ = if Tc.Env.debug env <| Options.Other "Rel" then Util.print2 "Imitating expressions: %s =?= %s\n" (Print.exp_to_string e1) (Print.exp_to_string e2) in
                let head2, args2 = Util.head_and_args_e e2 in
                let fvhead = Util.freevars_exp head2 in
                let occurs_ok, _ = occurs_check_e env (u1, t1) head2 in
                if Util.fvs_included fvhead Syntax.no_fvs && occurs_ok
                then let xs, tres = match Util.function_formals t1 with
                            | None -> [], t1
                            | Some (xs, c) -> xs, Util.comp_result c in
                     let gi_xi, gi_pi, f = sub_problems xs args2 in
                     let sol =
                        let body = mk_Exp_app'(head2, gi_xi) None e1.pos in
                        match xs with
                            | [] -> body
                            | _ -> mk_Exp_abs(xs, mk_Exp_app'(head2, gi_xi) None e1.pos) None e1.pos in
                     if Tc.Env.debug env <| Options.Other "Rel"
                     then Util.print3 "Imitated: %s -> %s\nSubprobs=\n%s\n" (Print.uvar_e_to_string (u1,t1)) (Print.exp_to_string sol) (gi_pi |> List.map (prob_to_string env) |> String.concat "\n");
                     solve env (attempt gi_pi (solve_prob orig (Some f) [UE((u1, t1), sol)] wl))
                else if occurs_ok
                then project_e head2 args2
                else giveup env "flex-rigid: occurs check failed" orig in


        begin match maybe_vars1 with
            | None
            | Some [] -> imitate_or_project_e ()
            | Some xs ->
                let fvs1 = freevars_of_binders xs in
                let fvs2 = Util.freevars_exp e2 in
                let occurs_ok, _ = occurs_check_e env (u1, t1) e2 in
                if Util.set_is_subset_of fvs2.ftvs fvs1.ftvs
                    && Util.set_is_subset_of fvs2.fxvs fvs1.fxvs
                    && occurs_ok
                then // U1 xs =?= e2
                     // U1 = \xs. e2
                    let sol = mk_Exp_abs'(xs, e2) None e1.pos in
                    solve env (solve_prob orig None [UE((u1,t1), sol)] wl)
                else imitate_or_project_e ()
        end in

    let flex_flex (e1, u1, t1, args1) (e2, u2, t2, args2) = //flex-flex: solve only patterns
      let maybe_vars1 = pat_vars env [] args1 in
      let maybe_vars2 = pat_vars env [] args2 in
      begin match maybe_vars1, maybe_vars2 with
        | None, _
        | _, None ->
          if wl.defer_ok
          then solve env (defer "flex-flex: not a pattern" orig wl)
          else giveup env "flex-flex expressions not patterns" orig

        | Some xs, Some ys ->
          if (Unionfind.equivalent u1 u2 && binders_eq xs ys)
          then solve env wl
          else
              //U1 xs =?= U2 ys
              //zs = xs intersect ys, U fresh
              //U1 = \x1 x2. U zs
              //U2 = \y1 y2 y3. U zs
              let zs = intersect_vars xs ys in
              let tt = Recheck.recompute_typ e2 in
              let u, _ = new_evar (Env.get_range env) zs tt in
              let sub1 = match xs with 
                | [] -> u
                | _ -> mk_Exp_abs(xs, u) (Some t1) e1.pos in
              let sub2 = match ys with 
                | [] -> u
                | _ -> mk_Exp_abs(ys, u) (Some t2) e1.pos in
              solve env (solve_prob orig None [UE((u1,t1), sub1); UE((u2,t2), sub2)] wl)
      end in

    let smt_fallback e1 e2 =
        if wl.smt_ok
        then let _ = if debug env <| Options.Other "Rel" then Util.print1 "Using SMT to solve:\n%s\n" (prob_to_string env orig) in
             let t, _ = new_tvar (Tc.Env.get_range env) (Tc.Env.binders env) ktype in
             solve env (solve_prob orig (Some <| Util.mk_eq t t e1 e2) [] wl)
        else giveup env "no SMT solution permitted" orig  in

    match e1.n, e2.n with
    | Exp_ascribed(e1, _, _), _ ->
      solve_e env ({problem with lhs=e1}) wl

    | _, Exp_ascribed(e2, _, _) ->
      solve_e env ({problem with rhs=e2}) wl

    | Exp_uvar _,                 Exp_uvar _
    | Exp_app({n=Exp_uvar _}, _), Exp_uvar _
    | Exp_uvar _,                 Exp_app({n=Exp_uvar _}, _)
    | Exp_app({n=Exp_uvar _}, _), Exp_app({n=Exp_uvar _}, _) -> //flex-flex
      flex_flex (destruct_flex_e e1) (destruct_flex_e e2)

    | Exp_uvar _, _
    | Exp_app({n=Exp_uvar _}, _), _ -> //flex-rigid
      flex_rigid (destruct_flex_e e1) e2

    | _, Exp_uvar _
    | _, Exp_app({n=Exp_uvar _}, _) -> //rigid-flex
      flex_rigid (destruct_flex_e e2) e1 //the constraint is an equality, so reorientation is fine

    //remaining are rigid-rigid; try to solve as much by unification,
    //falling back to SMT only when all else fails

    | Exp_bvar x1, Exp_bvar x1' ->
      if Util.bvd_eq x1.v x1'.v
      then solve env (solve_prob orig None [] wl)
      else solve env (solve_prob orig (Some <| Util.mk_eq (Recheck.recompute_typ e1) (Recheck.recompute_typ e2) e1 e2) [] wl)

    | Exp_fvar (fv1, _), Exp_fvar (fv1', _) ->
      if lid_equals fv1.v fv1'.v
      then solve env (solve_prob orig None [] wl)
      else giveup env "free-variables unequal" orig //distinct top-level free vars are never provably equal

    | Exp_constant s1, Exp_constant s1' ->
      let const_eq s1 s2 = match s1, s2 with
          | Const_bytearray(b1, _), Const_bytearray(b2, _) -> b1=b2
          | Const_string(b1, _), Const_string(b2, _) -> b1=b2
          | _ -> s1=s2 in
      if const_eq s1 s1'
      then solve env (solve_prob orig None [] wl)
      else giveup env "constants unequal" orig

    | Exp_app({n=Exp_abs _}, _), _ ->
      solve_e env ({problem with lhs=whnf_e env e1}) wl

    | _, Exp_app({n=Exp_abs _}, _) ->
      solve_e env ({problem with rhs=whnf_e env e2}) wl

    | Exp_app(head1, args1), Exp_app(head2, args2) ->
      let orig_wl = wl in
      let rec solve_args sub_probs wl args1 args2 = match args1, args2 with
            | [], [] ->
                let guard = Util.mk_conj_l (List.map p_guard sub_probs |> List.map fst) in
                let g = simplify_formula env guard in
                let g = Util.compress_typ g in
                begin match g.n with
                    | Typ_const fv when lid_equals fv.v Const.true_lid -> //if every sub-problem was solved by unification
                      solve env (solve_prob orig None wl.subst ({orig_wl with subst=[]})) //then solve the whole thing without any logical guard
                    | _ ->
                      let t, _ = new_tvar (Tc.Env.get_range env) (Tc.Env.binders env) ktype in
                      let guard = Util.mk_disj g (Util.mk_eq t t e1 e2) in
                      solve env (solve_prob orig (Some guard) wl.subst ({orig_wl with subst=[]})) //otherwise either try to prove the component guards, or the whole thing equal
                end
            | arg1::rest1, arg2::rest2 ->
                let prob = match fst arg1, fst arg2 with
                | Inl t1, Inl t2 ->
                    TProb <| mk_problem (p_scope orig) orig t1 EQ t2 None "expression type arg"
                | Inr e1, Inr e2 ->
                    EProb <| mk_problem (p_scope orig) orig e1 EQ e2 None "expression arg"
                | _ -> failwith "Impossible: ill-typed expression" in
                begin match solve env ({wl with defer_ok=false; smt_ok=false; attempting=[prob]; wl_deferred=[]}) with
                | Failed _ -> smt_fallback e1 e2
                | Success (subst, _) -> solve_args (prob::sub_probs) ({wl with subst=subst}) rest1 rest2
                end
            | _ -> failwith "Impossible: lengths defer" in


      let rec match_head_and_args head1 head2 = match (Util.compress_exp head1).n, (Util.compress_exp head2).n with
        | Exp_bvar x, Exp_bvar y           when (bvar_eq x y && List.length args1 = List.length args2) -> solve_args [] wl args1 args2
        | Exp_fvar (f, _), Exp_fvar (g, _) when (fvar_eq f g && not (Util.is_interpreted f.v) && List.length args1 = List.length args2) -> solve_args [] wl args1 args2
        | Exp_ascribed(e, _, _), _ -> match_head_and_args e head2
        | _, Exp_ascribed(e, _, _) -> match_head_and_args head1 e
        | Exp_abs _, _ ->
          solve_e env ({problem with lhs=whnf_e env e1}) wl
        | _, Exp_abs _ ->
          solve_e env ({problem with rhs=whnf_e env e2}) wl
        | _ -> smt_fallback e1 e2 in

     match_head_and_args head1 head2


    | _ -> //TODO: check that they at least have the same head?
     let t, _ = new_tvar (Tc.Env.get_range env) (Tc.Env.binders env) ktype in
     let guard = Util.mk_eq t t e1 e2 in
     if Tc.Env.debug env <| Options.Other "Rel"
     then Util.print1 "Emitting guard %s\n" (Print.typ_to_string guard);
     solve env (solve_prob orig (Some <| Util.mk_eq t t e1 e2) [] wl)

(* -------------------------------------------------------- *)
(* top-level interface                                      *)
(* -------------------------------------------------------- *)
type guard_formula =
  | Trivial
  | NonTrivial of formula

type implicits = list<either<(uvar_t * Range.range), (uvar_e * Range.range)>>
type guard_t = {
  guard_f:  guard_formula;
  deferred: deferred;
  implicits: implicits;
}

let guard_to_string (env:env) g =
  let form = match g.guard_f with
      | Trivial -> "trivial"
      | NonTrivial f ->
          if debug env <| Options.Other "Rel"
          then Normalize.formula_norm_to_string env f
          else "non-trivial" in
  let carry = List.map (fun (_, x) -> prob_to_string env x) g.deferred.carry |> String.concat ",\n" in
  Util.format2 "\n\t{guard_f=%s;\n\t deferred={\n%s};}\n" form carry

(* ------------------------------------------------*)
(* <guard_formula ops> Operations on guard_formula *)
(* ------------------------------------------------*)
let guard_of_guard_formula g = {guard_f=g; deferred={slack=[]; carry=[]}; implicits=[]}

let guard_form g = g.guard_f

let is_trivial g = match g with
    | {guard_f=Trivial; deferred={carry=[]; slack=[]}} -> true
    | _ -> false

let trivial_guard = {guard_f=Trivial; deferred={carry=[]; slack=[]}; implicits=[]}

let abstract_guard x g = match g with
    | None
    | Some ({guard_f=Trivial}) -> g
    | Some g ->
      let f = match g.guard_f with
        | NonTrivial f -> f
        | _ -> failwith "impossible" in
      Some ({g with guard_f=NonTrivial <| mk_Typ_lam([v_binder x], f) None f.pos})

let apply_guard g e = match g.guard_f with
  | Trivial -> g
  | NonTrivial f -> {g with guard_f=NonTrivial (syn f.pos (Some ktype) <| mk_Typ_app(f, [varg e]))}

let trivial t = match t with
  | Trivial -> ()
  | NonTrivial _ -> failwith "impossible"

let conj_guard_f g1 g2 = match g1, g2 with
  | Trivial, g
  | g, Trivial -> g
  | NonTrivial f1, NonTrivial f2 -> NonTrivial (Util.mk_conj f1 f2)

let check_trivial t = match t.n with
    | Typ_const tc when (lid_equals tc.v Const.true_lid) -> Trivial
    | _ -> NonTrivial t

let imp_guard_f g1 g2 = match g1, g2 with
  | Trivial, g -> g
  | g, Trivial -> Trivial
  | NonTrivial f1, NonTrivial f2 ->
    let imp = Util.mk_imp f1 f2 in check_trivial imp

let binop_guard f g1 g2 = {guard_f=f g1.guard_f g2.guard_f;
                           deferred={slack=g1.deferred.slack@g2.deferred.slack;
                                     carry=g1.deferred.carry@g2.deferred.carry};
                           implicits=g1.implicits@g2.implicits}
let conj_guard g1 g2 = binop_guard conj_guard_f g1 g2
let imp_guard g1 g2 = binop_guard imp_guard_f g1 g2

let close_guard binders g = match g.guard_f with
    | Trivial -> g
    | NonTrivial f -> {g with guard_f=close_forall binders f |> NonTrivial}

let mk_guard g ps slack locs = {guard_f=g;
                                deferred={carry=ps; slack=slack;};
                                implicits=[]}

(* ------------------------------------------------*)
(* </guard_formula ops>                            *)
(* ------------------------------------------------*)


let new_t_problem env lhs rel rhs elt loc =
 let reason = if debug env <| Other "ExplainRel"
              then Util.format3 "Top-level:\n%s\n\t%s\n%s" (Normalize.typ_norm_to_string env lhs) (rel_to_string rel) (Normalize.typ_norm_to_string env rhs)
              else "TOP" in
 let p = new_problem env lhs rel rhs elt loc reason in
 p

let new_t_prob env t1 rel t2 =
 let x = Util.gen_bvar_p (Env.get_range env) t1 in
 let env = Env.push_local_binding env (Env.Binding_var(x.v, x.sort)) in
 let p = new_t_problem env t1 rel t2 (Some <| Util.bvar_to_exp x) (Env.get_range env) in
 TProb p, x

let new_k_problem env lhs rel rhs elt loc =
 let reason = if debug env <| Other "ExplainRel"
              then Util.format3 "Top-level:\n%s\n\t%s\n%s" (Normalize.kind_norm_to_string env lhs) (rel_to_string rel) (Normalize.kind_norm_to_string env rhs)
              else "TOP" in
 let p = new_problem env lhs rel rhs elt loc reason in
 p

let simplify_guard env g = match g.guard_f with
    | Trivial -> g
    | NonTrivial f ->
      if Tc.Env.debug env Options.High then Util.print1 "Simplifying guard %s\n" (Print.typ_to_string f);
      let f = Normalize.norm_typ [Beta; Simplify] env f in
      let f = match f.n with
        | Typ_const fv when lid_equals fv.v Const.true_lid -> Trivial
        | _ -> NonTrivial f in
      {g with guard_f=f}

let solve_and_commit env probs err =
  let probs = if !Options.eager_inference then {probs with defer_ok=false} else probs in
  let sol = solve env probs in
  match sol with
    | Success (s, deferred) ->
      commit env s;
      Some deferred
    | Failed (d,s) ->
      if Tc.Env.debug env <| Options.Other "ExplainRel"
      then Util.print_string <| explain env d s;
      err (d,s)

let with_guard env prob dopt = match dopt with
    | None -> None
    | Some d ->
      Some <| simplify_guard env ({guard_f=(p_guard prob |> fst |> NonTrivial); deferred=d; implicits=[]})

let try_keq env k1 k2 : option<guard_t> =
  if debug env <| Other "Rel"
  then Util.print2 "try_keq of %s and %s\n" (Print.kind_to_string k1) (Print.kind_to_string k2);
  let prob = KProb <| new_k_problem env (norm_kind [Beta] env k1) EQ (norm_kind [Beta] env k2) None (Env.get_range env) in
  with_guard env prob <| solve_and_commit env (singleton env prob) (fun _ -> None)

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

let subkind env k1 k2 : guard_t =
 if debug env <| Other "Rel"
 then Util.print3 "(%s) subkind of %s and %s\n" (Range.string_of_range <| Env.get_range env) (Print.kind_to_string k1) (Print.kind_to_string k2);
 let prob = KProb <| new_k_problem env (whnf_k env k1) SUB (whnf_k env k2) None (Env.get_range env) in
 let res = Util.must (with_guard env prob <| solve_and_commit env (singleton env prob) (fun _ ->
    raise (Error(Tc.Errors.incompatible_kinds env k1 k2, Tc.Env.get_range env)))) in
// if debug env <| Other "Rel"
// then Util.fprint4 "(%s) subkind of %s and %s solved with %s\n"
//    (Range.string_of_range <| Env.get_range env) (Print.kind_to_string k1) (Print.kind_to_string k2) (guard_to_string env res);
 res

let try_teq env t1 t2 : option<guard_t> =
 if debug env <| Other "Rel"
 then Util.print2 "try_teq of %s and %s\n" (Print.typ_to_string t1) (Print.typ_to_string t2);
 let prob = TProb<| new_t_problem env t1 EQ t2 None (Env.get_range env) in
 let g = with_guard env prob <| solve_and_commit env (singleton env prob) (fun _ -> None) in
 g

let teq env t1 t2 : guard_t =
 match try_teq env t1 t2 with
    | None -> raise (Error(Tc.Errors.basic_type_error env None t2 t1, Tc.Env.get_range env))
    | Some g ->
      if debug env <| Other "Rel" then Util.print3 "teq of %s and %s succeeded with guard %s\n" (Print.typ_to_string t1) (Print.typ_to_string t2) (guard_to_string env g);
      g

let try_subtype env t1 t2 =
 if debug env <| Other "Rel"
 then Util.print2 "try_subtype of %s and %s\n" (Normalize.typ_norm_to_string env t1) (Normalize.typ_norm_to_string env t2);
 let prob, x = new_t_prob env t1 SUB t2 in
 let g = with_guard env prob <| solve_and_commit env (singleton env prob) (fun _ -> None) in
 if debug env <| Options.Other "Rel"
    && Util.is_some g
 then Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" (Normalize.typ_norm_to_string env t1) (Normalize.typ_norm_to_string env t2) (guard_to_string env (Util.must g));
 abstract_guard x g

let subtype_fail env t1 t2 =
    raise (Error(Tc.Errors.basic_type_error env None t2 t1, Tc.Env.get_range env))

let subtype env t1 t2 : guard_t =
  match try_subtype env t1 t2 with
    | Some f -> f
    | None -> subtype_fail env t1 t2

let sub_comp env c1 c2 =
  if debug env <| Other "Rel"
  then Util.print2 "sub_comp of %s and %s\n" (Print.comp_typ_to_string c1) (Print.comp_typ_to_string c2);
  let rel = if env.use_eq then EQ else SUB in
  let prob = CProb <| new_problem env c1 rel c2 None (Env.get_range env) "sub_comp" in
  with_guard env prob <| solve_and_commit env (singleton env prob)  (fun _ -> None)

let solve_deferred_constraints env (g:guard_t) =
   let fail (d,s) =
      let msg = explain env d s in
      raise (Error(msg, p_loc d)) in
   if Tc.Env.debug env <| Options.Other "Rel"
   && List.length g.deferred.carry <> 0
   then begin
    Util.print1 "Trying to solve carried problems: begin\n%s\nend\n"
   <| (g.deferred.carry |> List.map (fun (msg, x) -> Util.format4 "(At %s) %s\n%s\nguard is %s\n"
        (Range.string_of_range <| p_loc x) msg (prob_to_string env x) (Normalize.formula_norm_to_string env (p_guard x |> fst))) |> String.concat "\n")
   end;
   let gopt = solve_and_commit env (wl_of_guard env g.deferred) fail in
   match gopt with
    | Some ({slack=slack}) ->
      fix_slack_vars slack;
      {g with deferred=no_deferred}
    | _ -> failwith "impossible"

let try_discharge_guard env (g:guard_t) =
   let g = solve_deferred_constraints env g in
   if not (Options.should_verify env.curmodule.str) then ()
   else match g.guard_f with
    | Trivial -> ()
    | NonTrivial vc ->
        let vc = Normalize.norm_typ [DeltaHard; Beta; Eta; Simplify] env vc in
        begin match check_trivial vc with
            | Trivial -> ()
            | NonTrivial vc ->
                if Tc.Env.debug env <| Options.Other "Rel" then Tc.Errors.diag (Tc.Env.get_range env) (Util.format1 "Checking VC=\n%s\n" (Print.formula_to_string vc));
                env.solver.solve env vc
        end
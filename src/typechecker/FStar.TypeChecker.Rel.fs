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
module FStar.TypeChecker.Rel
open FStar.All

open FStar
open FStar.Util
open FStar.Errors
open FStar.TypeChecker
open FStar.Syntax
open FStar.TypeChecker.Env
open FStar.Syntax.Syntax
open FStar.Syntax.Subst
open FStar.Ident
open FStar.TypeChecker.Common
module BU = FStar.Util //basic util
module U = FStar.Syntax.Util
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module N = FStar.TypeChecker.Normalize

(* ------------------------------------------------*)
(* <guard_formula ops> Operations on guard_formula *)
(* ------------------------------------------------*)
let guard_of_guard_formula g = {guard_f=g; deferred=[]; univ_ineqs=([], []); implicits=[]}

let guard_form g = g.guard_f

let is_trivial g = match g with
    | {guard_f=Trivial; deferred=[]} -> true
    | _ -> false

let trivial_guard = {guard_f=Trivial; deferred=[]; univ_ineqs=([], []); implicits=[]}

let abstract_guard x g = match g with
    | None
    | Some ({guard_f=Trivial}) -> g
    | Some g ->
      let f = match g.guard_f with
        | NonTrivial f -> f
        | _ -> failwith "impossible" in
      Some ({g with guard_f=NonTrivial <| U.abs [mk_binder x] f (Some (mk_Total U.ktype0 |> U.lcomp_of_comp |> Inl))})

let apply_guard g e = match g.guard_f with
  | Trivial -> g
  | NonTrivial f -> {g with guard_f=NonTrivial <| mk (Tm_app(f, [as_arg e])) (Some U.ktype0.n) f.pos}

let map_guard g map = match g.guard_f with
  | Trivial -> g
  | NonTrivial f -> {g with guard_f=NonTrivial (map f)}

let trivial t = match t with
  | Trivial -> ()
  | NonTrivial _ -> failwith "impossible"

let conj_guard_f g1 g2 = match g1, g2 with
  | Trivial, g
  | g, Trivial -> g
  | NonTrivial f1, NonTrivial f2 -> NonTrivial (U.mk_conj f1 f2)

let check_trivial t = match t.n with
    | Tm_fvar tc when S.fv_eq_lid tc Const.true_lid -> Trivial
    | _ -> NonTrivial t

let imp_guard_f g1 g2 = match g1, g2 with
  | Trivial, g -> g
  | g, Trivial -> Trivial
  | NonTrivial f1, NonTrivial f2 ->
    let imp = U.mk_imp f1 f2 in check_trivial imp

let binop_guard f g1 g2 = {guard_f=f g1.guard_f g2.guard_f;
                           deferred=g1.deferred@g2.deferred;
                           univ_ineqs=(fst g1.univ_ineqs@fst g2.univ_ineqs,
                                       snd g1.univ_ineqs@snd g2.univ_ineqs);
                           implicits=g1.implicits@g2.implicits}
let conj_guard g1 g2 = binop_guard conj_guard_f g1 g2
let imp_guard g1 g2 = binop_guard imp_guard_f g1 g2

let close_guard_univs us bs g =
    match g.guard_f with
    | Trivial -> g
    | NonTrivial f ->
      let f =
          List.fold_right2 (fun u b f ->
              if Syntax.is_null_binder b then f
              else U.mk_forall u (fst b) f)
        us bs f in
    {g with guard_f=NonTrivial f}

let close_forall env bs f =
    List.fold_right (fun b f ->
            if Syntax.is_null_binder b then f
            else let u = env.universe_of env (fst b).sort in
                 U.mk_forall u (fst b) f)
    bs f

let close_guard env binders g =
    match g.guard_f with
    | Trivial -> g
    | NonTrivial f ->
      {g with guard_f=NonTrivial (close_forall env binders f)}

(* ------------------------------------------------*)
(* </guard_formula ops>                            *)
(* ------------------------------------------------*)

(* --------------------------------------------------------- *)
(* <new_uvar> Generating new unification variables/patterns  *)
(* --------------------------------------------------------- *)
let new_uvar r binders k =
  let uv = Unionfind.fresh Uvar in
  match binders with
    | [] ->
      let uv = mk (Tm_uvar(uv,k)) (Some k.n) r in
      uv, uv
    | _ ->
      let args = binders |> List.map U.arg_of_non_null_binder in
      let k' = U.arrow binders (mk_Total k) in
      let uv = mk (Tm_uvar(uv,k')) None r in
      mk (Tm_app(uv, args)) (Some k.n) r, uv
(* --------------------------------------------------------- *)
(* </new_uvar>                                               *)
(* --------------------------------------------------------- *)

let mk_eq2 env t1 t2 =
    (* NS: Rather than introducing a new variable, it would be much preferable
            to simply compute the type of t1 here.
            Sadly, it seems to be way too expensive to call env.type_of here.
    *)
    let t_type, u = U.type_u () in
    let tt, _ = new_uvar t1.pos (Env.all_binders env) t_type in
    U.mk_eq2 u tt t1 t2

(* Instantiation of unification variables *)
type uvi =
    | TERM of (uvar * typ)    * term
    | UNIV of S.universe_uvar * universe

(* The set of problems currently being addressed *)
type worklist = {
    attempting:  probs;
    wl_deferred: list<(int * string * prob)>;  //flex-flex cases, non patterns, and subtyping constraints involving a unification variable,
    ctr:         int;                          //a counter incremented each time we extend subst, used to detect if we've made progress
    defer_ok:    bool;                         //whether or not carrying constraints is ok---at the top-level, this flag is false
    smt_ok:      bool;                         //whether or not falling back to the SMT solver is permitted
    tcenv:       Env.env;
}

(* Types used in the output of the solver *)
type solution =
  | Success of deferred
  | Failed  of prob * string

type variance =
    | COVARIANT
    | CONTRAVARIANT
    | INVARIANT

type tprob = problem<typ, term>
type cprob = problem<comp, unit>
type problem_t<'a,'b> = problem<'a,'b>

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

let term_to_string env t =
    match (SS.compress t).n with
    | Tm_uvar(u, t) -> BU.format2 "(%s:%s)" (Print.uvar_to_string u) (Print.term_to_string t)
    | Tm_app({n=Tm_uvar(u, ty)}, args) ->
      BU.format3 "(%s:%s) %s" (Print.uvar_to_string u) (Print.term_to_string ty) (Print.args_to_string args)
    | _ -> Print.term_to_string t

let prob_to_string env = function
  | TProb p ->
    BU.format "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
        [(BU.string_of_int p.pid);
         (term_to_string env p.lhs);
         (Print.tag_of_term p.lhs);
         (rel_to_string p.relation);
         (term_to_string env p.rhs);
         (Print.tag_of_term p.rhs);
         (N.term_to_string env (fst p.logical_guard));
         (p.reason |> String.concat "\n\t\t\t")]
  | CProb p ->
    BU.format3 "\t%s \n\t\t%s\n\t%s"
                 (N.comp_to_string env p.lhs)
                 (rel_to_string p.relation)
                 (N.comp_to_string env p.rhs)

let uvi_to_string env = function
    | UNIV (u, t) ->
      let x = if (Options.hide_uvar_nums()) then "?" else Unionfind.uvar_id u |> string_of_int in
      BU.format2 "UNIV %s %s" x (Print.univ_to_string t)

    | TERM ((u,_), t) ->
      let x = if (Options.hide_uvar_nums()) then "?" else Unionfind.uvar_id u |> string_of_int in
      BU.format2 "TERM %s %s" x (N.term_to_string env t)
let uvis_to_string env uvis = List.map (uvi_to_string env) uvis |> String.concat  ", "
let names_to_string nms = BU.set_elements nms |> List.map Print.bv_to_string |> String.concat ", "
let args_to_string args = args |> List.map (fun (x, _) -> Print.term_to_string x) |> String.concat " "

(* ------------------------------------------------*)
(* </Printing> *)
(* ------------------------------------------------*)

(* ------------------------------------------------*)
(* <worklist ops> Operations on worklists          *)
(* ------------------------------------------------*)
let empty_worklist env = {
    attempting=[];
    wl_deferred=[];
    ctr=0;
    tcenv=env;
    defer_ok=not (Options.eager_inference());
    smt_ok=true
}
let singleton' env prob smt_ok   = {empty_worklist env with attempting=[prob]; smt_ok = smt_ok}
let singleton env prob           = singleton' env prob true
let wl_of_guard env g            = {empty_worklist env with defer_ok=false; attempting=List.map snd g}
let defer reason prob wl         = {wl with wl_deferred=(wl.ctr, reason, prob)::wl.wl_deferred}
let attempt probs wl             = {wl with attempting=probs@wl.attempting}

let giveup env reason prob =
    if debug env <| Options.Other "Rel"
    then BU.print2 "Failed %s:\n%s\n" reason (prob_to_string env prob);
    Failed(prob, reason)
(* ------------------------------------------------*)
(* </worklist ops>                                 *)
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
    | TProb p -> maybe_invert p |> TProb
    | CProb p -> maybe_invert p |> CProb
let vary_rel rel = function
    | INVARIANT -> EQ
    | CONTRAVARIANT -> invert_rel rel
    | COVARIANT -> rel
let p_pid = function
   | TProb p -> p.pid
   | CProb p -> p.pid
let p_rel = function
   | TProb p -> p.relation
   | CProb p -> p.relation
let p_reason = function
   | TProb p -> p.reason
   | CProb p -> p.reason
let p_loc = function
   | TProb p -> p.loc
   | CProb p -> p.loc
let p_guard = function
   | TProb p -> p.logical_guard
   | CProb p -> p.logical_guard
let p_scope = function
   | TProb p -> p.scope
   | CProb p -> p.scope
let p_invert = function
   | TProb p -> TProb <| invert p
   | CProb p -> CProb <| invert p
let is_top_level_prob p = p_reason p |> List.length = 1
let next_pid =
    let ctr = BU.mk_ref 0 in
    fun () -> incr ctr; !ctr

let mk_problem scope orig lhs rel rhs elt reason = {
     pid=next_pid();
     lhs=lhs;
     relation=rel;
     rhs=rhs;
     element=elt;
     logical_guard=new_uvar Range.dummyRange scope U.ktype0; //logical guards are always squashed;
                                                             //their range is intentionally dummy
     reason=reason::p_reason orig;
     loc=p_loc orig;
     rank=None;
     scope=scope;
}
let new_problem env lhs rel rhs elt loc reason =
  let scope = Env.all_binders env in
   {
    pid=next_pid();
    lhs=lhs;
    relation=rel;
    rhs=rhs;
    element=elt;
    logical_guard=new_uvar Range.dummyRange scope U.ktype0; //logical guards are always squashed?
                                                            //their range is intentionally dummy
    reason=[reason];
    loc=loc;
    rank=None;
    scope=scope;
   }
let problem_using_guard orig lhs rel rhs elt reason = {
     pid=next_pid();
     lhs=lhs;
     relation=rel;
     rhs=rhs;
     element=elt;
     logical_guard=p_guard orig;
     reason=reason::p_reason orig;
     loc=p_loc orig;
     rank=None;
     scope=p_scope orig;
}
let guard_on_element wl problem x phi =
    match problem.element with
        | None ->
          let u = wl.tcenv.universe_of wl.tcenv x.sort in
          U.mk_forall u x phi
        | Some e -> Subst.subst [NT(x,e)] phi
let explain env d s =
    if Env.debug env <| Options.Other "ExplainRel"
    then BU.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
                       (Range.string_of_range <| p_loc d)
                       (prob_to_string env d)
                       (p_reason d |> String.concat "\n\t>")
                       s
    else let d = maybe_invert_p d in
         let rel = match p_rel d with
            | EQ -> "equal to"
            | SUB -> "a subtype of"
            | _ -> failwith "impossible" in
         let lhs, rhs = match d with
            | TProb tp -> N.term_to_string env tp.lhs, N.term_to_string env tp.rhs
            | CProb cp -> N.comp_to_string env cp.lhs, N.comp_to_string env cp.rhs in
         BU.format3 "%s is not %s the expected type %s" lhs rel rhs


(* ------------------------------------------------*)
(* </prob ops>                                     *)
(* ------------------------------------------------*)


(* ------------------------------------------------*)
(* <uvi ops> Instantiating unification variables   *)
(* ------------------------------------------------*)
let commit uvis = uvis |> List.iter (function
    | UNIV(u, t)      ->
      begin match t with
        | U_unif u' -> Unionfind.union u u'
        | _ -> Unionfind.change u (Some t)
      end
    | TERM((u, _), t) -> U.set_uvar u t)

let find_term_uvar uv s = BU.find_map s (function
    | UNIV _ -> None
    | TERM((u,_), t) -> if Unionfind.equivalent uv u then Some t else None)

let find_univ_uvar u s = BU.find_map s (function
    | UNIV(u', t) -> if Unionfind.equivalent u u' then Some t else None
    | _ -> None)

(* ------------------------------------------------*)
(* </uvi ops>                                      *)
(* ------------------------------------------------*)


(* ------------------------------------------------*)
(* <normalization>                                *)
(* ------------------------------------------------*)
let whnf env t     = SS.compress (N.normalize [N.Beta; N.WHNF] env (U.unmeta t))
let sn env t       = SS.compress (N.normalize [N.Beta] env t)
let norm_arg env t = sn env (fst t), snd t
let sn_binders env (binders:binders) =
    binders |> List.map (fun (x, imp) -> {x with sort=sn env x.sort}, imp)

(*  norm_univ wl u
        Replace all unification variables in u with their solution in wl, if any
        And normalize the result
*)
let norm_univ wl u =
    let rec aux u =
        let u = SS.compress_univ u in
        match u with
            | U_succ u ->
              U_succ (aux u)

            | U_max us ->
              U_max (List.map aux us)

            | _ -> u in
    N.normalize_universe wl.tcenv (aux u)

let normalize_refinement steps env wl t0 = N.normalize_refinement steps env t0

let base_and_refinement env wl t1 =
   let rec aux norm t1 =
        match t1.n with
        | Tm_refine(x, phi) ->
            if norm
            then (x.sort, Some(x, phi))
            else begin match normalize_refinement [N.WHNF] env wl t1 with
                | {n=Tm_refine(x, phi)} -> (x.sort, Some(x, phi))
                | tt -> failwith (BU.format2 "impossible: Got %s ... %s\n" (Print.term_to_string tt) (Print.tag_of_term tt))
            end

        | Tm_uinst _
        | Tm_fvar _
        | Tm_app _ ->
            if norm
            then (t1, None)
            else let t1' = normalize_refinement [N.WHNF] env wl t1 in
                 begin match (SS.compress t1').n with
                            | Tm_refine _ -> aux true t1'
                            | _ -> t1, None
                 end

        | Tm_type _
        | Tm_constant _
        | Tm_name _
        | Tm_bvar _
        | Tm_arrow _
        | Tm_abs _
        | Tm_uvar _
        | Tm_let _
        | Tm_match _ -> (t1, None)

        | Tm_meta _
        | Tm_ascribed _  //NS: Why are the two previous cases excluded? Because of the whnf/unmeta
        | Tm_delayed _
        | Tm_unknown -> failwith (BU.format2 "impossible (outer): Got %s ... %s\n" (Print.term_to_string t1) (Print.tag_of_term t1)) in

   aux false (whnf env t1)

let unrefine env t = base_and_refinement env (empty_worklist env) t |> fst

let trivial_refinement t = S.null_bv t, U.t_true

let as_refinement env wl t =
    let t_base, refinement = base_and_refinement env wl t in
    match refinement with
        | None -> trivial_refinement t_base
        | Some (x, phi) -> x, phi

let force_refinement (t_base, refopt) =
    let y, phi = match refopt with
        | Some (y, phi) -> y, phi
        | None -> trivial_refinement t_base in
    mk (Tm_refine(y, phi)) None t_base.pos

(* ------------------------------------------------ *)
(* </normalization>                                 *)
(* ------------------------------------------------ *)

(* ------------------------------------------------ *)
(* <printing worklists>                             *)
(* ------------------------------------------------ *)

let wl_prob_to_string wl = function
  | TProb p ->
    BU.format4 "%s: %s  (%s)  %s"
        (string_of_int p.pid)
        (Print.term_to_string (whnf wl.tcenv p.lhs))
        (rel_to_string p.relation)
        (Print.term_to_string (whnf wl.tcenv p.rhs))

  | CProb p ->
    BU.format4 "%s: %s  (%s)  %s"
                 (string_of_int p.pid)
                 (N.comp_to_string wl.tcenv p.lhs)
                 (rel_to_string p.relation)
                 (N.comp_to_string wl.tcenv p.rhs)

let wl_to_string wl =
    List.map (wl_prob_to_string wl) (wl.attempting@(wl.wl_deferred |> List.map (fun (_, _, x) -> x))) |> String.concat "\n\t"

(* ------------------------------------------------ *)
(* </printing worklists>                             *)
(* ------------------------------------------------ *)

(* ------------------------------------------------ *)
(* <solving problems>                               *)
(* ------------------------------------------------ *)
let u_abs k ys t =
    let (ys, t), (xs, c) = match (SS.compress k).n with
        | Tm_arrow(bs, c) ->
          if List.length bs = List.length ys
          then (ys, t), SS.open_comp bs c
          else let ys', t, _ = U.abs_formals t in
               (ys@ys', t), U.arrow_formals_comp k
        | _ -> (ys, t), ([], S.mk_Total k) in
    if List.length xs <> List.length ys
    (* TODO : not putting any cflags here on the annotation... *)
    then U.abs ys t (Some (Inr (Const.effect_Tot_lid, []))) //The annotation is imprecise, due to a discrepancy in currying/eta-expansions etc.; causing a loss in precision for the SMT encoding
    else let c = Subst.subst_comp (U.rename_binders xs ys) c in
         U.abs ys t (U.lcomp_of_comp c |> Inl |> Some)

let solve_prob' resolve_ok prob logical_guard uvis wl =
    let phi = match logical_guard with
      | None -> U.t_true
      | Some phi -> phi in
    let _, uv = p_guard prob in
    let _ = match (Subst.compress uv).n with
        | Tm_uvar(uvar, k) ->
          let bs = p_scope prob in
          let phi = u_abs k bs phi in
          if Env.debug wl.tcenv <| Options.Other "Rel"
          then BU.print3 "Solving %s (%s) with formula %s\n"
                            (string_of_int (p_pid prob))
                            (Print.term_to_string uv)
                            (Print.term_to_string phi);
          U.set_uvar uvar phi
        | _ -> if not resolve_ok then failwith "Impossible: this instance has already been assigned a solution" in
    commit uvis;
    {wl with ctr=wl.ctr + 1}

let extend_solution pid sol wl =
    if Env.debug wl.tcenv <| Options.Other "RelCheck"
    then BU.print2 "Solving %s: with %s\n" (string_of_int pid) (List.map (uvi_to_string wl.tcenv) sol |> String.concat ", ");
    commit sol;
    {wl with ctr=wl.ctr+1}

let solve_prob prob logical_guard uvis wl =
    let conj_guard t g = match t, g with
        | _, Trivial -> t
        | None, NonTrivial f -> Some f
        | Some t, NonTrivial f -> Some (U.mk_conj t f) in
    if Env.debug wl.tcenv <| Options.Other "RelCheck"
    then BU.print2 "Solving %s: with %s\n" (string_of_int <| p_pid prob) (List.map (uvi_to_string wl.tcenv) uvis |> String.concat ", ");
    solve_prob' false prob logical_guard uvis wl

(* ------------------------------------------------ *)
(* </solving problems>                              *)
(* ------------------------------------------------ *)


(* ------------------------------------------------ *)
(* <variable ops> common ops on variables           *)
(* ------------------------------------------------ *)
let rec occurs (wl:worklist) (uk:(uvar * 'b)) (t:typ) =
    Free.uvars t
    |> BU.set_elements
    |> BU.for_some (fun (uv, _) ->
       Unionfind.equivalent uv (fst uk))

let occurs_check env wl uk t =
    let occurs_ok = not (occurs wl uk t) in
    let msg =
        if occurs_ok then None
        else Some (BU.format2 "occurs-check failed (%s occurs in %s)"
                        (Print.uvar_to_string (fst uk))
                        (Print.term_to_string t)) in
    occurs_ok, msg

let occurs_and_freevars_check env wl uk fvs t =
    let fvs_t = Free.names t in
    let occurs_ok, msg = occurs_check env wl uk t in
    (occurs_ok, BU.set_is_subset_of fvs_t fvs, (msg, fvs, fvs_t))

let intersect_vars v1 v2 =
    let as_set v =
        v |> List.fold_left (fun out x -> BU.set_add (fst x) out) S.no_names in
    let v1_set = as_set v1 in
    let isect, _ =
        v2 |> List.fold_left (fun (isect, isect_set) (x, imp) ->
            if not <| BU.set_mem x v1_set
            then //definitely not in the intersection
                 isect, isect_set
            else //maybe in the intersect, if its type is only dependent on prior elements in the telescope
                 let fvs = Free.names x.sort in
                 if BU.set_is_subset_of fvs isect_set
                 then (x, imp)::isect, BU.set_add x isect_set
                 else isect, isect_set)
        ([], S.no_names) in
    List.rev isect

let binders_eq v1 v2 =
  List.length v1 = List.length v2
  && List.forall2 (fun (a, _) (b, _) -> S.bv_eq a b) v1 v2

let pat_var_opt env seen arg =
   let hd = norm_arg env arg in
   match (fst hd).n with
    | Tm_name a ->
        if seen |> BU.for_some (fun (b, _) -> bv_eq a b)
        then None
        else Some (a, snd hd)

    | _ -> None

let rec pat_vars env seen args : option<binders> = match args with
    | [] -> Some (List.rev seen)
    | hd::rest ->
        begin match pat_var_opt env seen hd with
            | None -> if Env.debug env <| Options.Other "Rel" then BU.print1 "Not a pattern: %s\n" (Print.term_to_string <| fst hd); None //not a pattern
            | Some x -> pat_vars env (x::seen) rest
        end

let is_flex t = match (SS.compress t).n with
    | Tm_uvar _
    | Tm_app({n=Tm_uvar _}, _) -> true
    | _ -> false

let destruct_flex_t t = match t.n with
    | Tm_uvar(uv, k) -> (t, uv, k, [])
    | Tm_app({n=Tm_uvar(uv, k)}, args) -> (t, uv, k, args)
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

   It simplifies the unification algorithm to view every F* term
   as either a lambda, a variable, or the application of a constructor to some arguments.

   For the built-in term formers, i.e., Tm_arrow and Tm_refine,
   we need a way to decompose them into their sub-terms so that they
   appear in the form (C arg1 ... argn), for some constructor C.

   Question: What about let and match?
         let is a redex that can always take a step---so it is not handled here

         match can be stuck at the head, but its decomposition
         is very specialized. We must handle it separately.

   We call this operation 'decomposition'.

   To illustrate, consider decompose has the type:

   val decompose: env
               -> term
               -> (list<either<term, comp>> -> term)
                    * (term -> bool)
                    * list<(option<binder> * variance * either<term, comp>)>

   let recompose, matches, components = decompose_typ env t

        1. The components are the immediate sub-terms of t,
           with their contexts provided as a binders

           For example: if t = x1:t1 -> ... -> xn:tn -> C
           the components are ([(Some x1,  CONTRAVARIANT, t1);
                                ...;
                                ([Some xn, CONTRAVARIANT, tn);
                                ([None,    COVARIANT, C)]

        2. recompose is a function that rebuilds a t-like type from new subterms

           In our example, rebuild [s1;...;sn; C'] builds
                           x1:s1 -> ... -> xn:sn -> C'

           The shape of the argument to rebuild must match the shape of the components of t

           Also, the free names of {s1..sn, C'} should match the x1..xn of the original term,
           if they are to be scoped properly after recomposition.

        3. matches is function which decides whether or not
           a given type t' could be structurally similar to t (modulo reduction). It serves
           as a proxy for the constructor of the original type t

           For example, any Typ_fun head matches t
                        any Uvar    head matches t
                        any Typ_lam head matches t
                        any (t1 t2) head matches t, if t1 matches t

           where t matches t'
              if t head matches t'
              or t full matches t'
*)

type match_result =
  | MisMatch of option<delta_depth> * option<delta_depth>
  | HeadMatch
  | FullMatch

let head_match = function
    | MisMatch(i, j) -> MisMatch(i, j)
    | _ -> HeadMatch

let fv_delta_depth env fv = match fv.fv_delta with
    | Delta_abstract d ->
      if env.curmodule.str = fv.fv_name.v.nsstr
      then d //we're in the defining module
      else Delta_constant
    | Delta_defined_at_level _ ->
      begin match Env.lookup_definition [Unfold Delta_constant] env fv.fv_name.v with
            | None -> Delta_constant //there's no definition to unfold, e.g., because it's marked irreducible
            | _ -> fv.fv_delta
      end
    | d ->
      d

let rec delta_depth_of_term env t =
    let t = U.unmeta t in
    match t.n with
    | Tm_meta _
    | Tm_delayed _  -> failwith "Impossible"
    | Tm_unknown
    | Tm_bvar _
    | Tm_name _
    | Tm_uvar _
    | Tm_let _
    | Tm_match _ -> None
    | Tm_uinst(t, _)
    | Tm_ascribed(t, _, _)
    | Tm_app(t, _)
    | Tm_refine({sort=t}, _) -> delta_depth_of_term env t
    | Tm_constant _
    | Tm_type _
    | Tm_arrow _
    | Tm_abs _ -> Some Delta_constant
    | Tm_fvar fv -> Some (fv_delta_depth env fv)


let rec head_matches env t1 t2 : match_result =
  let t1 = U.unmeta t1 in
  let t2 = U.unmeta t2 in
  match t1.n, t2.n with
    | Tm_name x, Tm_name y -> if S.bv_eq x y then FullMatch else MisMatch(None, None)
    | Tm_fvar f, Tm_fvar g -> if S.fv_eq f g then FullMatch else MisMatch(Some (fv_delta_depth env f), Some (fv_delta_depth env g))
    | Tm_uinst (f, _), Tm_uinst(g, _) -> head_matches env f g |> head_match
    | Tm_constant c, Tm_constant d -> if c=d then FullMatch else MisMatch(None, None)
    | Tm_uvar (uv, _),  Tm_uvar (uv', _) -> if Unionfind.equivalent uv uv' then FullMatch else MisMatch(None, None)

    | Tm_refine(x, _), Tm_refine(y, _) -> head_matches env x.sort y.sort |> head_match

    | Tm_refine(x, _), _  -> head_matches env x.sort t2 |> head_match
    | _, Tm_refine(x, _)  -> head_matches env t1 x.sort |> head_match

    | Tm_type _, Tm_type _
    | Tm_arrow _, Tm_arrow _ -> HeadMatch

    | Tm_app(head, _), Tm_app(head', _) -> head_matches env head head' |> head_match
    | Tm_app(head, _), _ -> head_matches env head t2 |> head_match
    | _, Tm_app(head, _) -> head_matches env t1 head |> head_match

    | _ -> MisMatch(delta_depth_of_term env t1, delta_depth_of_term env t2)

(* Does t1 match t2, after some delta steps? *)
let head_matches_delta env wl t1 t2 : (match_result * option<(typ*typ)>) =
    let maybe_inline t =
        let head, _ = U.head_and_args t in
        match (U.un_uinst head).n with
        | Tm_fvar fv ->
          if Env.lookup_definition [Env.Eager_unfolding_only] env fv.fv_name.v |> Option.isSome
          then N.normalize [N.Beta; N.Eager_unfolding] env t |> Some
          else None
        | _ -> None
    in
    let success d r t1 t2 = (r, (if d>0 then Some(t1, t2) else None)) in
    let fail r = (r, None) in
    let rec aux retry n_delta t1 t2 =
        let r = head_matches env t1 t2 in
        match r with
            | MisMatch(Some Delta_equational, _)
            | MisMatch(_, Some Delta_equational) ->
              if not retry then fail r
              else begin match maybe_inline t1, maybe_inline t2 with
                   | None, None -> fail r
                   | Some t1, None -> aux false (n_delta + 1) t1 t2
                   | None, Some t2 -> aux false (n_delta + 1) t1 t2
                   | Some t1, Some t2 -> aux false (n_delta + 1) t1 t2
                   end

            | MisMatch(Some d1, Some d2) when (d1=d2) -> //incompatible
              begin match Common.decr_delta_depth d1 with
                | None ->
                  fail r

                | Some d ->
                  let t1 = normalize_refinement [N.UnfoldUntil d; N.WHNF] env wl t1 in
                  let t2 = normalize_refinement [N.UnfoldUntil d; N.WHNF] env wl t2 in
                  aux retry (n_delta + 1) t1 t2
              end

            | MisMatch(Some d1, Some d2) -> //these may be related after some delta steps
              let d1_greater_than_d2 = Common.delta_depth_greater_than d1 d2 in
              let t1, t2 = if d1_greater_than_d2
                           then let t1' = normalize_refinement [N.UnfoldUntil d2; N.WHNF] env wl t1 in
                                t1', t2
                           else let t2' = normalize_refinement [N.UnfoldUntil d1; N.WHNF] env wl t2 in
                                t1, normalize_refinement [N.UnfoldUntil d1; N.WHNF] env wl t2 in
              aux retry (n_delta + 1) t1 t2

            | MisMatch _ -> fail r

            | _ -> success n_delta r t1 t2 in
    aux true 0 t1 t2

type tc =
 | T of term * (binders -> Range.range -> term)
 | C of comp
type tcs = list<tc>

let generic_kind (binders:binders) r =
    let t, _ = U.type_u () in
    fst (new_uvar r binders t)
let kind_type (binders:binders) (r:Range.range) =
    U.type_u() |> fst

let rec decompose env t : (list<tc> -> term) * (term -> bool) * list<(option<binder> * variance * tc)> =
    let t = U.unmeta t in
    let matches t' = match head_matches env t t' with
        | MisMatch _ -> false
        | _ -> true in
    match t.n with
        | Tm_app(hd, args) -> (* easy case: it's already in the form we want *)
            let rebuild args' =
            let args = List.map2 (fun x y -> match x, y with
                | (_, imp), T (t, _) -> t, imp
                | _ -> failwith "Bad reconstruction") args args' in
            mk (Tm_app(hd, args)) None t.pos in

            let tcs = //each argument in order, with empty binders
            args |> List.map (fun (t, _) -> None, INVARIANT, T (t, generic_kind)) in

            rebuild, matches, tcs

        | Tm_arrow(bs, c) ->
            let fail () = failwith "Bad reconstruction" in
            let bs, c = Subst.open_comp bs c in

            let rebuild tcs =
                let rec aux out (bs:binders) tcs = match bs, tcs with
                    | (x, imp)::bs, T (t, _)::tcs -> aux (({x with sort=t},imp)::out) bs tcs
                    | [], [C c] -> U.arrow (List.rev out) c
                    | _ -> failwith "Bad reconstruction" in
                aux [] bs tcs in

            let rec decompose out = function
                | [] -> List.rev ((None, COVARIANT, C c)::out)
                | hd::rest ->
                  decompose ((Some hd, CONTRAVARIANT, T ((fst hd).sort, kind_type))::out) rest in

            rebuild,
            matches,
            decompose [] bs

        | _ ->
          let rebuild = function
            | [] -> t
            | _ -> failwith "Bad reconstruction" in

          rebuild, (fun t -> true), []

let un_T = function
    | T (t, _) -> t
    | _ -> failwith "Impossible"

let arg_of_tc = function
    | T (t, _) -> as_arg t
    | _ -> failwith "Impossible"

let imitation_sub_probs orig env scope (ps:args) (qs:list<(option<binder> * variance * tc)>) =
   //U p1..pn REL h q1..qm
   //if h is not a free variable
   //extend_subst: (U -> \x1..xn. h (G1(x1..xn), ..., Gm(x1..xm)))
   //sub-problems: Gi(p1..pn) REL' qi, where REL' = vary_rel REL (variance h i)
    let r = p_loc orig in
    let rel = p_rel orig in
    let sub_prob scope args q =
        match q with
        | _, variance, T (ti, mk_kind) ->
            let k = mk_kind scope r in
            let gi_xs, gi = new_uvar r scope k in
            let gi_ps = match args with
                | [] -> gi
                | _ -> mk (Tm_app(gi, args)) None r in
            T (gi_xs, mk_kind),
            TProb <| mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm"

        | _, _, C _ -> failwith "impos" in

    let rec aux scope args qs : (list<prob> * list<tc> * formula) =
        match qs with
            | [] -> [], [], U.t_true
            | q::qs ->
                let tc, probs = match q with
                     | bopt, variance, C ({n=Total (ti, uopt)}) ->
                       begin match sub_prob scope args (bopt, variance, T (ti, kind_type)) with
                            | T (gi_xs, _), prob -> C <| mk_Total' gi_xs uopt, [prob]
                            | _ -> failwith "impossible"
                       end

                     | bopt, variance, C ({n=GTotal(ti, uopt)}) ->
                       begin match sub_prob scope args (bopt, variance, T (ti, kind_type)) with
                            | T (gi_xs, _), prob -> C <| mk_GTotal' gi_xs uopt, [prob]
                            | _ -> failwith "impossible"
                       end

                     |_, _, C ({n=Comp c}) ->
                       let components = c.effect_args |> List.map (fun t -> (None, INVARIANT, T (fst t, generic_kind))) in
                       let components = (None, COVARIANT, T (c.result_typ, kind_type))::components in
                       let tcs, sub_probs = List.map (sub_prob scope args) components |> List.unzip in
                       let gi_xs = mk_Comp <| {
                            comp_univs=c.comp_univs;
                            effect_name=c.effect_name;
                            result_typ=List.hd tcs |> un_T;
                            effect_args=List.tl tcs |> List.map arg_of_tc;
                            flags=c.flags
                        }  in
                        C gi_xs, sub_probs

                    | _ ->
                      let ktec, prob = sub_prob scope args q in
                      ktec, [prob] in

                let bopt, scope, args = match q with
                    | Some b, _, _ -> Some b, b::scope, U.arg_of_non_null_binder b::args
                    | _ -> None, scope, args in

                let sub_probs, tcs, f = aux scope args qs in
                let f = match bopt with
                    | None -> U.mk_conj_l (f:: (probs |> List.map (fun prob -> p_guard prob |> fst)))
                    | Some b ->
                      let u_b = env.universe_of env (fst b).sort in
                      U.mk_conj_l (U.mk_forall u_b (fst b) f :: (probs |> List.map (fun prob -> p_guard prob |> fst))) in

                probs@sub_probs, tc::tcs, f in

   aux scope ps qs

(* ------------------------------------------------ *)
(* </decomposition>                                 *)
(* ------------------------------------------------ *)

(* ----------------------------------------------------- *)
(* Ranking problems for the order in which to solve them *)
(* ----------------------------------------------------- *)
type flex_t = (term * uvar * typ * args)
type im_or_proj_t = ((uvar * typ) * binders * comp)
                    * list<arg>  //invariant: length args = length binders
                    * ((list<tc> -> typ) * (typ -> bool) * list<(option<binder> * variance * tc)>)

let rigid_rigid       = 0
let flex_rigid_eq     = 1
let flex_refine_inner = 2
let flex_refine       = 3
let flex_rigid        = 4
let rigid_flex        = 5
let refine_flex       = 6
let flex_flex         = 7
let compress_tprob wl p = {p with lhs=whnf wl.tcenv p.lhs; rhs=whnf wl.tcenv p.rhs}

let compress_prob wl p = match p with
    | TProb p -> compress_tprob wl p |> TProb
    | CProb _ -> p


let rank wl pr : int    //the rank
                 * prob   //the input problem, pre-processed a bit (the wl is needed for the pre-processing)
                 =
   let prob = compress_prob wl pr |> maybe_invert_p in
   match prob with
    | TProb tp ->
      let lh, _ = U.head_and_args tp.lhs in
      let rh, _ = U.head_and_args tp.rhs in
      let rank, tp = begin match lh.n, rh.n with
        | Tm_uvar _, Tm_uvar _ -> flex_flex, tp

        | Tm_uvar _, _
        | _, Tm_uvar _ when (tp.relation=EQ || Options.eager_inference()) -> flex_rigid_eq, tp

        | Tm_uvar _, _ ->
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

        | _, Tm_uvar _ ->
          let b, ref_opt = base_and_refinement wl.tcenv wl tp.lhs in
          begin match ref_opt with
            | None -> rigid_flex, tp
            | _ -> refine_flex, {tp with lhs=force_refinement (b, ref_opt)}
          end

        | _, _ -> rigid_rigid, tp
      end in
      rank, {tp with rank=Some rank} |> TProb

    | CProb cp -> rigid_rigid, {cp with rank=Some rigid_rigid} |> CProb

let next_prob wl : option<prob>  //a problem with the lowest rank, or a problem whose rank <= flex_rigid_eq, if any
                 * list<prob>    //all the other problems in wl
                 * int           //the rank of the first problem, or the minimum rank in the wl
                 =
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
let is_rigid_flex rank = rigid_flex <= rank && rank <= refine_flex

(* ----------------------------------------------------- *)
(* Solving universe equalities                           *)
(* ----------------------------------------------------- *)
type univ_eq_sol =
  | UDeferred of worklist
  | USolved   of worklist
  | UFailed   of string

let rec really_solve_universe_eq pid_orig wl u1 u2 =
    let u1 = N.normalize_universe wl.tcenv u1 in
    let u2 = N.normalize_universe wl.tcenv u2 in
    let rec occurs_univ v1 u = match u with
        | U_max us ->
          us |> BU.for_some (fun u ->
            let k, _ = U.univ_kernel u in
            match k with
                | U_unif v2 -> Unionfind.equivalent v1 v2
                | _ -> false)
        | _ -> occurs_univ v1 (U_max [u]) in

    let try_umax_components u1 u2 msg =
        match u1, u2 with
            | U_max us1, U_max us2 ->
              if List.length us1 = List.length us2 //go for a structural match
              then let rec aux wl us1 us2 = match us1, us2 with
                        | u1::us1, u2::us2 ->
                          begin match really_solve_universe_eq pid_orig wl u1 u2 with
                            | USolved wl ->
                                aux wl us1 us2
                            | failed -> failed
                          end
                        | _ -> USolved wl in
                    aux wl us1 us2
              else UFailed (BU.format2 "Unable to unify universes: %s and %s" (Print.univ_to_string u1) (Print.univ_to_string u2))

            | U_max us, u'
            | u', U_max us ->
                let rec aux wl us = match us with
                | [] -> USolved wl
                | u::us ->
                    begin match really_solve_universe_eq pid_orig wl u u' with
                    | USolved wl ->
                      aux wl us
                    | failed -> failed
                    end
                in aux wl us

            | _ -> UFailed (BU.format3 "Unable to unify universes: %s and %s (%s)" (Print.univ_to_string u1) (Print.univ_to_string u2) msg) in

    match u1, u2 with
        | U_bvar _, _
        | U_unknown, _
        | _, U_bvar _
        | _, U_unknown -> failwith (BU.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                                        (Print.univ_to_string u1)
                                        (Print.univ_to_string u2))

        | U_name x, U_name y ->
          if x.idText = y.idText
          then USolved wl
          else UFailed "Incompatible universes"

        | U_zero, U_zero ->
          USolved wl

        | U_succ u1, U_succ u2 ->
          really_solve_universe_eq pid_orig wl u1 u2

        | U_unif v1, U_unif v2 ->
          if Unionfind.equivalent v1 v2
          then USolved wl
          else let wl = extend_solution pid_orig [UNIV(v1, u2)] wl in
               USolved wl

        | U_unif v1, u
        | u, U_unif v1 ->
          let u = norm_univ wl u in
          if occurs_univ v1 u
          then try_umax_components u1 u2
                (BU.format2 "Failed occurs check: %s occurs in %s" (Print.univ_to_string (U_unif v1)) (Print.univ_to_string u))
          else USolved (extend_solution pid_orig [UNIV(v1, u)] wl)

        | U_max _, _
        | _, U_max _ ->
          if wl.defer_ok
          then UDeferred wl
          else let u1 = norm_univ wl u1 in
               let u2 = norm_univ wl u2 in
               if U.eq_univs u1 u2
               then USolved wl
               else try_umax_components u1 u2 ""

        | U_succ _, U_zero
        | U_succ _, U_name _
        | U_zero,   U_succ _
        | U_zero,   U_name _
        | U_name _, U_succ _
        | U_name _, U_zero ->
          UFailed "Incompatible universes"

let solve_universe_eq orig wl u1 u2 =
    if wl.tcenv.lax_universes
    then USolved wl
    else really_solve_universe_eq orig wl u1 u2


let match_num_binders (bc1: (list<'a> * (list<'a> -> 'b)))
                      (bc2: (list<'a> * (list<'a> -> 'b)))
    : (list<'a> * 'b) * (list<'a> * 'b) =
    let (bs1, mk_cod1) = bc1 in
    let (bs2, mk_cod2) = bc2 in
    let curry n bs (mk_cod:(list<'a> -> 'b)) =
        let bs, rest = BU.first_N n bs in
        (bs, mk_cod rest)
    in
    let l1 = List.length bs1 in
    let l2 = List.length bs2 in
    if l1 = l2
    then (bs1, mk_cod1 []), (bs2, mk_cod2 [])
    else if l1 > l2
    then curry l2 bs1 mk_cod1, (bs2, mk_cod2 [])
    else (bs1, mk_cod1 []), curry l1 bs2 mk_cod2


(******************************************************************************************************)
(* Main solving algorithm begins here *)
(******************************************************************************************************)
let rec solve (env:Env.env) (probs:worklist) : solution =
//    printfn "Solving TODO:\n%s;;" (List.map prob_to_string probs.attempting |> String.concat "\n\t");
    if Env.debug env <| Options.Other "RelCheck"
    then BU.print1 "solve:\n\t%s\n" (wl_to_string probs);
    match next_prob probs with
       | Some hd, tl, rank ->
         let probs = {probs with attempting=tl} in
         begin match hd with
            | CProb cp ->
              solve_c env (maybe_invert cp) probs

            | TProb tp ->
              if not probs.defer_ok
              && flex_refine_inner <= rank
              && rank <= flex_rigid
              then match solve_flex_rigid_join env tp probs with
                    | None -> solve_t' env (maybe_invert tp) probs //giveup env "join doesn't exist" hd
                    | Some wl -> solve env wl
              else if not probs.defer_ok
                   && rigid_flex <= rank
                   && rank <= refine_flex
              then match solve_rigid_flex_meet env tp probs with
                    | None -> solve_t' env (maybe_invert tp) probs //giveup env "meet doesn't exist" hd
                    | Some wl -> solve env wl
              else solve_t' env (maybe_invert tp) probs
         end

       | None, _, _ ->
         match probs.wl_deferred with
            | [] ->
              Success [] //Yay ... done!

            | _ ->
              let attempt, rest = probs.wl_deferred |> List.partition (fun (c, _, _) -> c < probs.ctr) in
              match attempt with
                 | [] -> //can't solve yet; defer the rest
                   Success(List.map (fun (_, x, y) -> (x, y)) probs.wl_deferred)

                 | _ ->
                   solve env ({probs with attempting=attempt |> List.map (fun (_, _, y) -> y); wl_deferred=rest})

and solve_one_universe_eq (env:Env.env) (orig:prob) (u1:universe) (u2:universe) (wl:worklist) : solution =
    match solve_universe_eq (p_pid orig) wl u1 u2 with
        | USolved wl ->
          solve env (solve_prob orig None [] wl)

        | UFailed msg ->
          giveup env msg orig

        | UDeferred wl ->
          solve env (defer "" orig wl)

and solve_maybe_uinsts (env:Env.env) (orig:prob) (t1:term) (t2:term) (wl:worklist) : univ_eq_sol =
    let rec aux wl us1 us2 = match us1, us2 with
        | [], [] -> USolved wl

        | u1::us1, u2::us2 ->
          begin match solve_universe_eq (p_pid orig) wl u1 u2 with
            | USolved wl ->
              aux wl us1 us2

            | failed_or_deferred -> failed_or_deferred
          end

        | _ -> UFailed "Unequal number of universes" in

    let t1 = whnf env t1 in
    let t2 = whnf env t2 in
    match t1.n, t2.n with
        | Tm_uinst({n=Tm_fvar f}, us1), Tm_uinst({n=Tm_fvar g}, us2) ->
            let b = S.fv_eq f g in
            assert b;
            aux wl us1 us2

        | Tm_uinst _, _
        | _, Tm_uinst _ ->
            failwith "Impossible: expect head symbols to match"

        | _ ->
            USolved wl

and giveup_or_defer (env:Env.env) (orig:prob) (wl:worklist) (msg:string) : solution =
    if wl.defer_ok
    then begin
        if Env.debug env <| Options.Other "Rel"
        then BU.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" (prob_to_string env orig) msg;
        solve env (defer msg orig wl)
    end
    else giveup env msg orig

(******************************************************************************************************)
(* The case where t1 < u, ..., tn < u: we solve this by taking u=t1\/...\/tn                          *)
(******************************************************************************************************)
and solve_rigid_flex_meet (env:Env.env) (tp:tprob) (wl:worklist) : option<worklist> =
    if Env.debug env <| Options.Other "RelCheck"
    then BU.print1 "Trying to solve by meeting refinements:%s\n" (string_of_int tp.pid);
    let u, args = U.head_and_args tp.rhs in

    let rec disjoin t1 t2 : option<(term * list<prob>)> =
        let mr, ts = head_matches_delta env () t1 t2 in
        match mr with
            | MisMatch _ ->
              None

            | FullMatch ->
              begin match ts with
                | None -> Some (t1, [])
                | Some (t1, t2) ->
                  Some (t1, [])
              end

            | HeadMatch ->
              let t1, t2 = match ts with
                | Some (t1, t2) -> SS.compress t1, SS.compress t2
                | None -> SS.compress t1, SS.compress t2 in
              let eq_prob t1 t2 =
                  TProb <| new_problem env t1 EQ t2 None t1.pos "meeting refinements" in
              begin match t1.n, t2.n with
                | Tm_refine(x, phi1), Tm_refine(y, phi2) ->
                  Some (mk (Tm_refine(x, U.mk_disj phi1 phi2)) None t1.pos, [eq_prob x.sort y.sort])

                | _, Tm_refine(x, _) ->
                  Some (t1, [eq_prob x.sort t1])

                | Tm_refine (x, _), _ ->
                  Some (t2, [eq_prob x.sort t2])

                | _ ->
                  let head1, _ = U.head_and_args t1 in
                  begin match (U.un_uinst head1).n with
                    | Tm_fvar {fv_delta=Delta_defined_at_level i} ->
                      let prev = if i > 1
                                 then Delta_defined_at_level (i - 1)
                                 else Delta_constant in
                      let t1 = N.normalize [N.WHNF; N.UnfoldUntil prev] env t1 in
                      let t2 = N.normalize [N.WHNF; N.UnfoldUntil prev] env t2 in
                      disjoin t1 t2
                    | _ ->  //head matches but no way to take the meet; TODO, generalize to handle function types, constructed types, etc.
                      None
                  end
               end in

   let tt = u in//compress env wl u in
    match tt.n with
        | Tm_uvar(uv, _) ->
          //find all other constraints of the form t <: u
          let lower_bounds, rest = wl.attempting |> List.partition (function
            | TProb tp ->
                begin match tp.rank with
                    | Some rank when is_rigid_flex rank ->
                      let u', _ = U.head_and_args tp.rhs in
                      begin match (whnf env u').n with
                        | Tm_uvar(uv', _) -> Unionfind.equivalent uv uv'
                        | _ -> false
                      end
                    | _ -> false
                end
           | _ -> false) in

          let rec make_lower_bound (bound, sub_probs) tps = match tps with
            | [] -> Some (bound, sub_probs)
            | (TProb hd)::tl ->
              begin match disjoin bound (whnf env hd.lhs) with
                    | Some(bound, sub) -> make_lower_bound (bound, sub@sub_probs) tl
                    | None -> None
              end
            | _ -> None in

          begin match make_lower_bound (whnf env tp.lhs, []) lower_bounds with
            | None ->
              if Env.debug env <| Options.Other "RelCheck"
              then BU.print_string "No lower bounds\n";
              None

            | Some (lhs_bound, sub_probs) ->
              let eq_prob = new_problem env lhs_bound EQ tp.rhs None tp.loc "meeting refinements" in
              let _ = if Env.debug env <| Options.Other "RelCheck"
                      then let wl' = {wl with attempting=TProb eq_prob::sub_probs} in
                           BU.print1 "After meeting refinements: %s\n" (wl_to_string wl') in
              match solve_t env eq_prob ({wl with attempting=sub_probs}) with
                | Success _ ->
                  let wl = {wl with attempting=rest} in
                  let wl = solve_prob' false (TProb tp) None [] wl in
                  let _ = List.fold_left (fun wl p -> solve_prob' true p None [] wl) wl lower_bounds in
                  Some wl
                | _ -> None
          end

      | _ -> failwith "Impossible: Not a rigid-flex"

(******************************************************************************************************)
(* The case where u < t1, .... u < tn: we solve this by taking u=t1/\.../\tn                          *)
(******************************************************************************************************)
and solve_flex_rigid_join  (env:env) (tp:tprob) (wl:worklist) : option<worklist> =
    if Env.debug env <| Options.Other "RelCheck"
    then BU.print1 "Trying to solve by joining refinements:%s\n" (string_of_int tp.pid);
    let u, args = U.head_and_args tp.lhs in
    let ok, head_match, partial_match, fallback, failed_match = 0,1,2,3,4 in
    let max i j = if i < j then j else i in

    let base_types_match t1 t2 : option<list<prob>> =
        let h1, args1 = U.head_and_args t1 in
        let h2, _ = U.head_and_args t2 in
        match h1.n, h2.n with
        | Tm_fvar tc1, Tm_fvar tc2 ->
          if S.fv_eq tc1 tc2
          then if List.length args1 = 0
               then Some []
               else Some [TProb <| new_problem env t1 EQ t2 None t1.pos "joining refinements"]
          else None

        | Tm_name a, Tm_name b ->
          if S.bv_eq a b
          then if List.length args1 = 0
               then Some []
               else Some [TProb <| new_problem env t1 EQ t2 None t1.pos "joining refinements"]
          else None

        | _ -> None in

    let conjoin t1 t2 = match t1.n, t2.n with
        | Tm_refine(x, phi1), Tm_refine(y, phi2) ->
          let m = base_types_match x.sort y.sort in
          begin match m with
            | None -> None
            | Some m ->
              let x = freshen_bv x in
              let subst = [DB(0, x)] in
              let phi1 = SS.subst subst phi1 in
              let phi2 = SS.subst subst phi2 in
              Some (U.refine x (U.mk_conj phi1 phi2), m)
          end

        | _, Tm_refine(y, _) ->
          let m = base_types_match t1 y.sort in
          begin match m with
            | None -> None
            | Some m -> Some (t2, m)
          end

        | Tm_refine(x, _), _ ->
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
        | Tm_uvar(uv, _) ->
          //find all other constraints of the form uv <: t
          let upper_bounds, rest = wl.attempting |> List.partition (function
            | TProb tp ->
                begin match tp.rank with
                    | Some rank when is_flex_rigid rank ->
                      let u', _ = U.head_and_args tp.lhs in
                      begin match (whnf env u').n with
                        | Tm_uvar(uv', _) -> Unionfind.equivalent uv uv'
                        | _ -> false
                      end
                    | _ -> false
                end
           | _ -> false) in

          let rec make_upper_bound (bound, sub_probs) tps = match tps with
            | [] -> Some (bound, sub_probs)
            | (TProb hd)::tl ->
              begin match conjoin bound (whnf env hd.rhs) with
                    | Some(bound, sub) -> make_upper_bound (bound, sub@sub_probs) tl
                    | None -> None
              end
            | _ -> None in

          begin match make_upper_bound (whnf env tp.rhs, []) upper_bounds with
            | None ->
              if Env.debug env <| Options.Other "RelCheck"
              then BU.print_string "No upper bounds\n";
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
              let _ = if Env.debug env <| Options.Other "RelCheck"
                      then let wl' = {wl with attempting=TProb eq_prob::sub_probs} in
                           BU.print1 "After joining refinements: %s\n" (wl_to_string wl') in
              match solve_t env eq_prob ({wl with attempting=sub_probs}) with
                | Success _ ->
                  let wl = {wl with attempting=rest} in
                  let wl = solve_prob' false (TProb tp) None [] wl in
                  let _ = List.fold_left (fun wl p -> solve_prob' true p None [] wl) wl upper_bounds in
                  Some wl
                | _ -> None
          end

      | _ -> failwith "Impossible: Not a flex-rigid"

and solve_binders (env:Env.env) (bs1:binders) (bs2:binders) (orig:prob) (wl:worklist)
                  (rhs:binders -> Env.env -> list<subst_elt> -> prob) : solution =

   let rec aux scope env subst (xs:binders) (ys:binders) : either<(probs * formula), string> =
        match xs, ys with
            | [], [] ->
              let rhs_prob = rhs (List.rev scope) env subst in
              if debug env <| Options.Other "Rel"
              then BU.print1 "rhs_prob = %s\n" (prob_to_string env rhs_prob);
              let formula = p_guard rhs_prob |> fst in
              Inl ([rhs_prob], formula)

            | (hd1, imp)::xs, (hd2, imp')::ys when (imp=imp') ->
               let hd1 = {hd1 with sort=Subst.subst subst hd1.sort} in //open both binders
               let hd2 = {hd2 with sort=Subst.subst subst hd2.sort} in
               let prob = TProb <| mk_problem scope orig hd1.sort (invert_rel <| p_rel orig) hd2.sort None "Formal parameter" in
               let hd1 = freshen_bv hd1 in
               let subst = DB(0, hd1)::SS.shift_subst 1 subst in  //extend the substitution
               let env = Env.push_bv env hd1 in
               begin match aux ((hd1,imp)::scope) env subst xs ys with
                 | Inl (sub_probs, phi) ->
                   let phi =
                        U.mk_conj (p_guard prob |> fst)
                                  (close_forall env [(hd1,imp)] phi) in
                   if debug env <| Options.Other "Rel"
                   then BU.print2 "Formula is %s\n\thd1=%s\n" (Print.term_to_string phi) (Print.bv_to_string hd1);
                   Inl (prob::sub_probs, phi)

                 | fail -> fail
               end

           | _ -> Inr "arity or argument-qualifier mismatch" in

   let scope = p_scope orig in //Env.bound_vars env |> List.map S.mk_binder in
   match aux scope env [] bs1 bs2 with
    | Inr msg -> giveup env msg orig
    | Inl (sub_probs, phi) ->
      let wl = solve_prob orig (Some phi) [] wl in
      solve env (attempt sub_probs wl)

and solve_t (env:Env.env) (problem:tprob) (wl:worklist) : solution =
    solve_t' env (compress_tprob wl problem) wl

and solve_t' (env:Env.env) (problem:tprob) (wl:worklist) : solution =
    let giveup_or_defer orig msg = giveup_or_defer env orig wl msg in

    (* <rigid_rigid_delta>: are t1 and t2, with head symbols head1 and head2, compatible after some delta steps? *)
    let rigid_rigid_delta (env:Env.env) (orig:prob) (wl:worklist)
                          (head1:term) (head2:term) (t1:term) (t2:term)
        : solution =
        let m, o = head_matches_delta env wl t1 t2 in
        match m, o  with
            | (MisMatch _, _) -> //heads definitely do not match
                let may_relate head =
                    match (U.un_uinst head).n with
                    | Tm_name _
                    | Tm_match _ -> true
                    | Tm_fvar tc -> tc.fv_delta = Delta_equational
                    | _ -> false  in
                if (may_relate head1 || may_relate head2) && wl.smt_ok
                then let guard =
                        if problem.relation = EQ
                        then mk_eq2 env t1 t2
                        else let has_type_guard t1 t2 =
                                match problem.element with
                                    | Some t -> U.mk_has_type t1 t t2
                                    | None ->
                                    let x = S.new_bv None t1 in
                                    let u_x = env.universe_of env t1 in
                                    U.mk_forall u_x x (U.mk_has_type t1 (S.bv_to_name x) t2) in
                             if problem.relation = SUB
                             then has_type_guard t1 t2
                             else has_type_guard t2 t1 in
                    solve env (solve_prob orig (Some guard) [] wl)
                else giveup env "head mismatch" orig

            | (_, Some (t1, t2)) -> //heads match after some delta steps
                solve_t env ({problem with lhs=t1; rhs=t2}) wl

            | (_, None) -> //head1 matches head1, without delta
                if debug env <| Options.Other "Rel"
                then BU.print4 "Head matches: %s (%s) and %s (%s)\n"
                    (Print.term_to_string t1) (Print.tag_of_term t1)
                    (Print.term_to_string t2) (Print.tag_of_term t2);
                let head1, args1 = U.head_and_args t1 in
                let head2, args2 = U.head_and_args t2 in
                let nargs = List.length args1 in
                if nargs <> List.length args2
                then giveup env (BU.format4 "unequal number of arguments: %s[%s] and %s[%s]"
                            (Print.term_to_string head1)
                            (args_to_string args1)
                            (Print.term_to_string head2)
                            (args_to_string args2))
                            orig
                else if nargs=0 || U.eq_args args1 args2=U.Equal //special case: for easily proving things like nat <: nat, or greater_than i <: greater_than i etc.
                then match solve_maybe_uinsts env orig head1 head2 wl with
                        | USolved wl -> solve env (solve_prob orig None [] wl)
                        | UFailed msg -> giveup env msg orig
                        | UDeferred wl -> solve env (defer "universe constraints" orig wl)
                else//Given T t1 ..tn REL T s1..sn
                    //  if T expands to a refinement, then normalize it and recurse
                    //  This allows us to prove things like
                    //         type T (x:int) (y:int) = z:int{z = x + y}
                    //         T 0 1 <: T 1 0
                    //  By expanding out the definitions
                    //
                    //Otherwise, we reason extensionally about T and try to prove the arguments equal, i.e, ti = si, for all i
                    let base1, refinement1 = base_and_refinement env wl t1 in
                    let base2, refinement2 = base_and_refinement env wl t2 in
                    begin match refinement1, refinement2 with
                            | None, None ->  //neither side is a refinement; reason extensionally
                              begin match solve_maybe_uinsts env orig head1 head2 wl with
                                | UFailed msg -> giveup env msg orig
                                | UDeferred wl -> solve env (defer "universe constraints" orig wl)
                                | USolved wl ->
                                    let subprobs = List.map2 (fun (a, _) (a', _) -> TProb <| mk_problem (p_scope orig) orig a EQ a' None "index") args1 args2 in
                                    let formula = U.mk_conj_l (List.map (fun p -> fst (p_guard p)) subprobs) in
                                    let wl = solve_prob orig (Some formula) [] wl in
                                    solve env (attempt subprobs wl)
                              end

                            | _ ->
                                let lhs = force_refinement (base1, refinement1) in
                                let rhs = force_refinement (base2, refinement2) in
                                solve_t env ({problem with lhs=lhs; rhs=rhs}) wl
                    end in
    (* <rigid_rigid_delta> *)


    (* <imitate> used in flex-rigid *)
    let imitate orig (env:Env.env) (wl:worklist) (p:im_or_proj_t) : solution =
        let ((u,k), xs, c), ps, (h, _, qs) = p in
        let xs = sn_binders env xs in
        //U p1..pn REL h q1..qm
        //if h is not a free variable
        //extend_subst: (U -> \x1..xn. h (G1(x1..xn), ..., Gm(x1..xm)))
        //sub-problems: Gi(p1..pn) REL' qi, where REL' = vary_rel REL (variance h i)
        let r = Env.get_range env in
        let sub_probs, gs_xs, formula = imitation_sub_probs orig env xs ps qs in
        let im = U.abs xs (h gs_xs) (U.lcomp_of_comp c |> Inl |> Some) in
        if Env.debug env <| Options.Other "Rel"
        then BU.print6 "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
            (Print.binders_to_string ", " xs)
            (Print.comp_to_string c)
            (Print.term_to_string im) (Print.tag_of_term im)
            (List.map (prob_to_string env) sub_probs |> String.concat ", ")
            (N.term_to_string env formula);
        let wl = solve_prob orig (Some formula) [TERM((u,k), im)] wl in
        solve env (attempt sub_probs wl) in
    (* </imitate> *)

    let imitate' orig env wl = function
        | None -> giveup env "unable to compute subterms" orig
        | Some p ->imitate orig env wl p in

    (* <project> used in flex_rigid *)
    let project orig (env:Env.env) (wl:worklist) (i:int) (p:im_or_proj_t) : option<solution> =
        let (u, xs, c), ps, (h, matches, qs) = p in
        //U p1..pn REL h q1..qm
        //extend subst: U -> \x1..xn. xi(G1(x1...xn) ... Gk(x1..xm)) ... where k is the arity of ti
        //sub-problems: pi(G1(p1..pn)..Gk(p1..pn)) REL h q1..qm
        let r = Env.get_range env in
        let pi, _ = List.nth ps i in
        let xi, _ = List.nth xs i in

        let rec gs k =
            let bs, k = U.arrow_formals k in
            let rec aux subst bs = match bs with
                | [] -> [], []
                | (a, _)::tl ->
                    let k_a = SS.subst subst a.sort in
                    let gi_xs, gi = new_uvar r xs k_a in
                    let gi_xs = N.eta_expand env gi_xs in
                    let gi_ps = mk_Tm_app gi ps (Some k_a.n) r in
                    let subst = NT(a, gi_xs)::subst in
                    let gi_xs', gi_ps' = aux subst tl in
                    as_arg gi_xs::gi_xs', as_arg gi_ps::gi_ps' in
              aux [] bs in

        if not <| matches pi
        then None
        else let g_xs, _ = gs xi.sort in
             let xi = S.bv_to_name xi in
             let proj = U.abs xs (S.mk_Tm_app xi g_xs None r) (U.lcomp_of_comp c |> Inl |> Some) in
             let sub = TProb <| mk_problem (p_scope orig) orig (S.mk_Tm_app proj ps None r) (p_rel orig) (h <| List.map (fun (_, _, y) -> y) qs) None "projection" in
             if debug env <| Options.Other "Rel" then BU.print2 "Projecting %s\n\tsubprob=%s\n" (Print.term_to_string proj) (prob_to_string env sub);
             let wl = solve_prob orig (Some (fst <| p_guard sub)) [TERM(u, proj)] wl in
             Some <| solve env (attempt [sub] wl) in
    (* </project_t> *)

    (* <flex-rigid> *)
    let solve_t_flex_rigid (patterns_only:bool) (orig:prob)
                           (lhs:(flex_t * option<binders>)) (t2:typ) (wl:worklist)
        : solution =
        let (t1, uv, k_uv, args_lhs), maybe_pat_vars = lhs in
        let subterms ps : option<im_or_proj_t> =
            let xs, c = U.arrow_formals_comp k_uv in
            if List.length xs = List.length ps //easy, common case
            then Some (((uv,k_uv),xs,c), ps, decompose env t2)
            else let k_uv = N.normalize [N.Beta] env k_uv in
                 let rec elim k args : option<(binders * comp)> =
                     match (SS.compress k).n, args with
                     | _, [] -> Some ([], S.mk_Total k)
                     | Tm_uvar _, _
                     | Tm_app _, _ -> //k=?u x1..xn
                       let uv, uv_args = U.head_and_args k in
                       begin match (SS.compress uv).n with
                        | Tm_uvar (uvar, _) ->
                          (match pat_vars env [] uv_args with
                           | None -> None
                           | Some scope ->
                             let xs = args |> List.map (fun _ ->
                                Syntax.mk_binder <|
                                    Syntax.new_bv (Some k.pos)
                                                  (fst (new_uvar k.pos scope (U.type_u () |> fst)))) in
                             let c = S.mk_Total (fst (new_uvar k.pos scope (U.type_u () |> fst))) in
                             let k' = U.arrow xs c in
                             let uv_sol = U.abs scope k' (Some (Inl (U.lcomp_of_comp <| S.mk_Total (U.type_u () |> fst)))) in
                             Unionfind.change uvar (Fixed uv_sol);
                             Some (xs, c))
                        | _ -> None
                       end
                     | Tm_arrow(xs, c), _ ->
                       let n_args = List.length args in
                       let n_xs = List.length xs in
                       if n_xs = n_args
                       then SS.open_comp xs c |> Some
                       else if n_xs < n_args
                       then let args, rest = BU.first_N n_xs args in
                            let xs, c = SS.open_comp xs c in
                            BU.bind_opt
                                   (elim (U.comp_result c) rest)
                                   (fun (xs', c) -> Some (xs@xs', c))
                       else //n_args < n_xs
                            let xs, rest = BU.first_N n_args xs in
                            let t = mk (Tm_arrow(rest, c)) None k.pos in
                            SS.open_comp xs (S.mk_Total t) |> Some
                     | _ -> failwith (BU.format3 "Impossible: ill-typed application %s : %s\n\t%s"
                                        (Print.uvar_to_string uv)
                                        (Print.term_to_string k)
                                        (Print.term_to_string k_uv)) in
                BU.bind_opt
                    (elim k_uv ps)
                    (fun (xs, c) -> Some (((uv, k_uv), xs, c), ps, decompose env t2)) in

        let rec imitate_or_project (n:int) (stopt:option<im_or_proj_t>) (i:int) : solution =
            if i >= n || Option.isNone stopt
            then giveup env "flex-rigid case failed all backtracking attempts" orig
            else let st = Option.get stopt in
                 let tx = Unionfind.new_transaction () in
                 if i = -1
                 then match imitate orig env wl st with
                        | Failed _ ->
                          Unionfind.rollback tx;
                          imitate_or_project n stopt (i + 1) //backtracking point
                        | sol -> //no need to commit; we'll commit the enclosing transaction at the top-level
                          sol
                 else match project orig env wl i st with
                        | None
                        | Some (Failed _) ->
                          Unionfind.rollback tx;
                          imitate_or_project n stopt (i + 1) //backtracking point
                        | Some sol -> sol in

        let check_head fvs1 t2 =
            let hd, _ = U.head_and_args t2 in
            match hd.n with
                | Tm_arrow _
                | Tm_constant _
                | Tm_abs _  -> true
                | _ ->
                    let fvs_hd = Free.names hd in
                    if BU.set_is_subset_of fvs_hd fvs1
                    then true
                    else (if Env.debug env <| Options.Other "Rel"
                          then BU.print1 "Free variables are %s" (names_to_string fvs_hd); false) in

        let imitate_ok t2 = (* -1 means begin by imitating *)
            let fvs_hd = U.head_and_args t2 |> fst |> Free.names in
            if BU.set_is_empty fvs_hd
            then -1 (* yes, start by imitating *)
            else 0 (* no, start by projecting *) in

        match maybe_pat_vars with
          | Some vars ->
            let t1 = sn env t1 in
            let t2 = sn env t2 in
            let fvs1 = Free.names t1 in
            let fvs2 = Free.names t2 in
            let occurs_ok, msg = occurs_check env wl (uv,k_uv) t2 in
            if not occurs_ok
            then giveup_or_defer orig ("occurs-check failed: " ^ (Option.get msg))
            else if BU.set_is_subset_of fvs2 fvs1
            then (if not patterns_only
                  && U.is_function_typ t2
                  && p_rel orig <> EQ //function types have structural subtyping and have to be imitated
                  then imitate' orig env wl (subterms args_lhs)
                  else //fast solution, pattern equality
                    let _  = if debug env <| Options.Other "Rel"
                             then BU.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                    (Print.term_to_string t1)
                                    (names_to_string fvs1)
                                    (names_to_string fvs2) in
                    let sol = match vars with
                        | [] -> t2
                        | _ -> u_abs k_uv (sn_binders env vars) t2 in
                    let wl = solve_prob orig None [TERM((uv,k_uv), sol)] wl in
                    solve env wl)
            else if not patterns_only
                 && wl.defer_ok
                 && p_rel orig <> EQ
            then solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl)
            else if not patterns_only
                 && check_head fvs1 t2
            then let _ = if debug env <| Options.Other "Rel"
                            then BU.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                            (Print.term_to_string t1)
                                            (names_to_string fvs1)
                                            (names_to_string fvs2) in
                    imitate_or_project (List.length args_lhs) (subterms args_lhs) (-1)
            else giveup env "free-variable check failed on a non-redex" orig

          | None when patterns_only ->
                giveup env "not a pattern" orig

          | None ->
                if wl.defer_ok
                then solve env (defer "not a pattern" orig wl)
                else if check_head (Free.names t1) t2
                then let im_ok = imitate_ok t2 in
                     let _ = if debug env <| Options.Other "Rel"
                             then BU.print2 "Not a pattern (%s) ... %s\n"
                                                (Print.term_to_string t1) (if im_ok < 0 then "imitating" else "projecting") in
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
            (* A quasi pattern is a U x1...xn, where not all the xi are distinct
            *)
           let all_formals, _ = U.arrow_formals k in
           assert (List.length all_formals = List.length args);

            let rec aux pat_args              (* pattern arguments, so far *)
                        pattern_vars          (* corresponding formals *)
                        pattern_var_set       (* formals a set of bvs *)
                        formals               (* remaining formals to examine *)
                        args                  (* remaining actuals, same number as formals *)
                        : uvi * flex_t =
              match formals, args with
                | [], [] ->
                    let pat_args = List.rev pat_args |> List.map (fun (x, imp) -> (S.bv_to_name x, imp)) in
                    let pattern_vars = List.rev pattern_vars in
                    let kk =
                        let t, _ = U.type_u() in
                        fst (new_uvar t.pos pattern_vars t) in
                    let t', tm_u1 = new_uvar t.pos pattern_vars kk in
                    let _, u1, k1, _ = destruct_flex_t t' in
                    let sol = TERM((u,k), u_abs k all_formals t') in
                    let t_app = S.mk_Tm_app tm_u1 pat_args None t.pos  in
                    sol, (t_app, u1, k1, pat_args)

                | formal::formals, hd::tl ->
                  begin match pat_var_opt env pat_args hd with
                    | None -> //hd is not a pattern var
                      aux pat_args pattern_vars pattern_var_set formals tl

                    | Some y -> //hd=y and does not occur in pat_args
                      let maybe_pat = match xs_opt with
                        | None -> true
                        | Some xs -> xs |> BU.for_some (fun (x, _) -> S.bv_eq x (fst y)) in //it's in the intersection

                      if not maybe_pat
                      then aux pat_args pattern_vars pattern_var_set formals tl
                      else //for y to be a pattern var, the type of formal has to be dependent (at most) on the other pattern_vars
                          let fvs = Free.names (fst y).sort in
                          if not (BU.set_is_subset_of fvs pattern_var_set)
                          then //y can't be a pattern variable ... its type is dependent on a non-pattern variable
                               aux pat_args pattern_vars pattern_var_set formals tl
                          else aux (y::pat_args) (formal::pattern_vars) (BU.set_add (fst formal) pattern_var_set) formals tl
                  end

                 | _ -> failwith "Impossible" in

           aux [] [] (S.new_bv_set()) all_formals args in


        let solve_both_pats wl (u1, k1, xs, args1) (u2, k2, ys, args2) r =
            if Unionfind.equivalent u1 u2
            && binders_eq xs ys
            then solve env (solve_prob orig None [] wl)
            else //(U1:k1) xs =?= (U2:k2) ys
                 //    where k1 = bs -> k1' bs
                 //          k2 = cs -> k2' cs
                 //zs = xs intersect ys, (U:k_u) fresh
                 //     where k_u = ds -> k_u' ds
                 //U1 = \x1 x2. U zs
                 //U2 = \y1 y2 y3. U zs
                 //sub probs:
                 //k1' xs =?= k2' ys
                 //k_u zs =?= k1' xs   (an optimization drops this case when for k1'=Type _ \/ k2'=Type)
                let xs = sn_binders env xs in
                let ys = sn_binders env ys in
                let zs = intersect_vars xs ys in
                if Env.debug env <| Options.Other "Rel"
                then BU.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                        (Print.binders_to_string ", " xs) (Print.binders_to_string ", " ys) (Print.binders_to_string ", " zs)
                        (Print.term_to_string k1) (Print.term_to_string k2);
                let subst_k k xs args : term =
                    let xs_len = List.length xs in
                    let args_len = List.length args in
                    if xs_len = args_len
                    then Subst.subst (U.subst_of_list xs args) k
                    else if args_len < xs_len
                    then let xs, xs_rest = BU.first_N args_len xs in
                         let k = U.arrow xs_rest (S.mk_GTotal k) in
                         Subst.subst (U.subst_of_list xs args) k
                    else failwith (BU.format3 "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                    (Print.term_to_string k)
                                    (Print.binders_to_string ", " xs)
                                    (Print.args_to_string args)) in
                let k_u', sub_probs =
                    let bs, k1' = U.arrow_formals (N.normalize [N.Beta] env k1) in
                    let cs, k2' = U.arrow_formals (N.normalize [N.Beta] env k2) in
                    let k1'_xs = subst_k k1' bs args1 in
                    let k2'_ys = subst_k k2' cs args2 in
                    let sub_prob = TProb <| mk_problem (p_scope orig) orig k1'_xs EQ k2'_ys None "flex-flex kinding" in
                    match (SS.compress k1').n, (SS.compress k2').n with
                    | Tm_type _, _ ->
                      k1', [sub_prob]
                    | _, Tm_type _ ->
                      k2', [sub_prob]
                    | _ ->
                      let t, _ = U.type_u() in
                      let k_zs, _ = new_uvar r zs t in
                      let kprob = TProb <| mk_problem (p_scope orig) orig k1'_xs EQ k_zs None "flex-flex kinding" in
                      k_zs, [sub_prob; kprob] in
                let u_zs, knew1, knew2 =
                    fst <| new_uvar r zs k_u',
                    U.arrow xs (S.mk_Total k_u'),
                    U.arrow ys (S.mk_Total k_u') in
                let sub1 = u_abs knew1 xs u_zs in
                let occurs_ok, msg = occurs_check env wl (u1,k1) sub1 in
                if not occurs_ok
                then giveup_or_defer orig "flex-flex: failed occcurs check"
                else let sol1 = TERM((u1, k1), sub1) in
                     if Unionfind.equivalent u1 u2
                     then let wl = solve_prob orig None [sol1] wl in
                          solve env wl
                     else let sub2 = u_abs knew2 ys u_zs in
                          let occurs_ok, msg = occurs_check env wl (u2,k2) sub2 in
                          if not occurs_ok
                          then giveup_or_defer orig "flex-flex: failed occurs check"
                          else let sol2 = TERM((u2,k2), sub2) in
                               let wl = solve_prob orig None [sol1;sol2] wl in
                               solve env (attempt sub_probs wl)
        in

        let solve_one_pat (t1, u1, k1, xs) (t2, u2, k2, args2) =
            begin
                if Env.debug env <| Options.Other "Rel"
                then BU.print2 "Trying flex-flex one pattern (%s) with %s\n" (Print.term_to_string t1) (Print.term_to_string t2);
                if Unionfind.equivalent u1 u2
                then let sub_probs = List.map2
                         (fun (a, _) (t2, _) -> mk_problem (p_scope orig) orig (S.bv_to_name a) EQ t2 None "flex-flex index" |> TProb)
                         xs args2 in
                     let guard = U.mk_conj_l (List.map (fun p -> p_guard p |> fst) sub_probs) in
                     let wl = solve_prob orig (Some guard) [] wl in
                     solve env (attempt sub_probs wl)
                else
                     let t2 = sn env t2 in
                     let rhs_vars = Free.names t2 in
                     let occurs_ok, _ = occurs_check env wl (u1,k1) t2 in
                     let lhs_vars = Free.names_of_binders xs in
                     if occurs_ok
                     && BU.set_is_subset_of rhs_vars lhs_vars
                     then let sol = TERM((u1, k1), u_abs k1 xs t2) in
                          let wl = solve_prob orig None [sol] wl in
                          solve env wl
                     else if occurs_ok && not <| wl.defer_ok
                     then let sol, (_, u2, k2, ys) = force_quasi_pattern (Some xs) (t2, u2, k2, args2) in
                          let wl = extend_solution (p_pid orig) [sol] wl in
                          let _ = if Env.debug env <| Options.Other "QuasiPattern"
                                  then BU.print1 "flex-flex quasi pattern (2): %s\n" (uvi_to_string env sol) in
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
            | Some xs, Some ys ->
              solve_both_pats wl (u1, k1, xs, args1) (u2, k2, ys, args2) t2.pos
            | Some xs, None ->
              solve_one_pat (t1, u1, k1, xs) rhs
            | None, Some ys ->
              solve_one_pat (t2, u2, k2, ys) lhs
            | _ ->
              if wl.defer_ok
              then giveup_or_defer orig "flex-flex: neither side is a pattern"
              else let sol, _ = force_quasi_pattern None (t1, u1, k1, args1) in
                   let wl = extend_solution (p_pid orig) [sol] wl in
                   let _ = if Env.debug env <| Options.Other "QuasiPattern"
                           then BU.print1 "flex-flex quasi pattern (1): %s\n" (uvi_to_string env sol) in
                   match orig with
                    | TProb p -> solve_t env p wl
                    | _ -> giveup env "impossible" orig  in
    (* </flex-flex> *)

    let orig = TProb problem in
    if BU.physical_equality problem.lhs problem.rhs then solve env (solve_prob orig None [] wl) else
    let t1 = problem.lhs in
    let t2 = problem.rhs in
    if BU.physical_equality t1 t2 then solve env (solve_prob orig None [] wl) else
    let _ =
        if debug env (Options.Other "RelCheck")
        then BU.print1 "Attempting %s\n" (string_of_int problem.pid) in
    let r = Env.get_range env in

    match t1.n, t2.n with
      | Tm_bvar _, _
      | _, Tm_bvar _ -> failwith "Only locally nameless! We should never see a de Bruijn variable"

      | Tm_type u1, Tm_type u2 ->
        solve_one_universe_eq env orig u1 u2 wl

      | Tm_arrow(bs1, c1), Tm_arrow(bs2, c2) ->
        let mk_c c = function
            | [] -> c
            | bs -> mk_Total(mk (Tm_arrow(bs, c)) None c.pos) in

        let (bs1, c1), (bs2, c2) =
            match_num_binders (bs1, mk_c c1) (bs2, mk_c c2) in

        solve_binders env bs1 bs2 orig wl
        (fun scope env subst  ->
            let c1 = Subst.subst_comp subst c1 in
            let c2 = Subst.subst_comp subst c2 in //open both comps
            let rel = if (Options.use_eq_at_higher_order()) then EQ else problem.relation in
            CProb <| mk_problem scope orig c1 rel c2 None "function co-domain")

      | Tm_abs(bs1, tbody1, lopt1), Tm_abs(bs2, tbody2, lopt2) ->
        let mk_t t l = function
            | [] -> t
            | bs -> mk (Tm_abs(bs, t, l)) None t.pos in
        let (bs1, tbody1), (bs2, tbody2) =
            match_num_binders (bs1, mk_t tbody1 lopt1) (bs2, mk_t tbody2 lopt2) in
        solve_binders env bs1 bs2 orig wl
        (fun scope env subst ->
            TProb <| mk_problem scope orig (Subst.subst subst tbody1)
                                           problem.relation
                                           (Subst.subst subst tbody2) None "lambda co-domain")

      | Tm_abs _, _
      | _, Tm_abs _ ->
        let is_abs t = match t.n with
            | Tm_abs _ -> true
            | _ -> false in
        let maybe_eta t =
            if is_abs t then Inl t
            else let t = N.eta_expand wl.tcenv t in
                 if is_abs t then Inl t else Inr t in
        begin match maybe_eta t1, maybe_eta t2 with
            | Inl t1, Inl t2 ->
              solve_t env ({problem with lhs=t1; rhs=t2}) wl
            | Inl t_abs, Inr not_abs
            | Inr not_abs, Inl t_abs ->
              //we lack the type information to eta-expand properly
              //so, this is going to fail, except if one last shot succeeds
              if is_flex not_abs //if it's a pattern and the free var check succeeds, then unify it with the abstraction in one step
              && p_rel orig = EQ
              then solve_t_flex_rigid true orig (destruct_flex_pattern env not_abs) t_abs wl
              else giveup env "head tag mismatch: RHS is an abstraction" orig
            | _ -> failwith "Impossible: at least one side is an abstraction"
        end

      | Tm_refine _, Tm_refine _ ->
        let x1, phi1 = as_refinement env wl t1 in
        let x2, phi2 = as_refinement env wl t2 in
        let base_prob = TProb <| mk_problem (p_scope orig) orig x1.sort problem.relation x2.sort problem.element "refinement base type" in
        let x1 = freshen_bv x1 in
        let subst = [DB(0, x1)] in
        let phi1 = Subst.subst subst phi1 in
        let phi2 = Subst.subst subst phi2 in
        let env = Env.push_bv env x1 in
        let mk_imp imp phi1 phi2 = imp phi1 phi2 |> guard_on_element wl problem x1 in
        let fallback () =
            let impl =
                if problem.relation = EQ
                then mk_imp U.mk_iff phi1 phi2
                else mk_imp U.mk_imp phi1 phi2 in
            let guard = U.mk_conj (p_guard base_prob |> fst) impl in
            let wl = solve_prob orig (Some guard) [] wl in
            solve env (attempt [base_prob] wl) in
        if problem.relation = EQ
        then let ref_prob = TProb <| mk_problem (mk_binder x1 :: p_scope orig) orig phi1 EQ phi2 None "refinement formula" in
             begin match solve env ({wl with defer_ok=false; attempting=[ref_prob]; wl_deferred=[]}) with
                    | Failed _ -> fallback()
                    | Success _ ->
                      let guard =
                        U.mk_conj (p_guard base_prob |> fst)
                                  (p_guard ref_prob |> fst |> guard_on_element wl problem x1) in
                      let wl = solve_prob orig (Some guard) [] wl in
                      let wl = {wl with ctr=wl.ctr+1} in
                      solve env (attempt [base_prob] wl)
             end
        else fallback()

      (* flex-flex *)
      | Tm_uvar _,                Tm_uvar _
      | Tm_app({n=Tm_uvar _}, _), Tm_uvar _
      | Tm_uvar _,                Tm_app({n=Tm_uvar _}, _)
      | Tm_app({n=Tm_uvar _}, _), Tm_app({n=Tm_uvar _}, _) ->
        flex_flex orig (destruct_flex_t t1) (destruct_flex_t t2)

      (* flex-rigid equalities *)
      | Tm_uvar _, _
      | Tm_app({n=Tm_uvar _}, _), _ when (problem.relation=EQ) -> (* just imitate/project ... no slack *)
        solve_t_flex_rigid false orig (destruct_flex_pattern env t1) t2 wl

      (* rigid-flex: reorient if it is an equality constraint *)
      | _, Tm_uvar _
      | _, Tm_app({n=Tm_uvar _}, _) when (problem.relation = EQ) ->
        solve_t env (invert problem) wl

      (* flex-rigid: ?u _ <: Type _ *)
      (* flex-rigid: ?u _ <: t1 -> t2 *)
      | Tm_uvar _, Tm_type _
      | Tm_app({n=Tm_uvar _}, _), Tm_type _
      | Tm_uvar _, Tm_arrow _
      | Tm_app({n=Tm_uvar _}, _), Tm_arrow _ ->
        //this case is so common, that even though we could delay, it is almost always ok to solve it immediately as an equality
        //besides, in the case of arrows, if we delay it, the arity of various terms built by the unifier goes awry
        //so, don't delay!
        solve_t' env ({problem with relation=EQ}) wl

      (* flex-rigid: subtyping *)
      | Tm_uvar _, _
      | Tm_app({n=Tm_uvar _}, _), _ -> (* equate with the base type of the refinement on the RHS, and add a logical guard for the refinement formula *)
        if wl.defer_ok
        then solve env (defer "flex-rigid subtyping deferred" orig wl)
        else
            let new_rel = problem.relation in
            if not <| is_top_level_prob orig //If it's not top-level and t2 is refined, then we should not try to prove that t2's refinement is saturated
            then solve_t_flex_rigid false (TProb <| {problem with relation=new_rel}) (destruct_flex_pattern env t1) t2 wl
            else let t_base, ref_opt = base_and_refinement env wl t2 in
                 begin match ref_opt with
                        | None -> //no useful refinement on the RHS, so just equate and solve
                          solve_t_flex_rigid false (TProb <| {problem with relation=new_rel}) (destruct_flex_pattern env t1) t_base wl

                        | Some (y, phi) ->
                          let y' = {y with sort = t1} in
                          let impl = guard_on_element wl problem y' phi in
                          let base_prob =
                            TProb <| mk_problem problem.scope orig t1 new_rel y.sort problem.element "flex-rigid: base type" in
                          let guard = U.mk_conj (p_guard base_prob |> fst) impl in
                          let wl = solve_prob orig (Some guard) [] wl in
                          solve env (attempt [base_prob] wl)
                 end

      (* rigid-flex: subtyping *)
      | _, Tm_uvar _
      | _, Tm_app({n=Tm_uvar _}, _) -> (* widen immediately, by forgetting the top-level refinement and equating *)
        if wl.defer_ok
        then solve env (defer "rigid-flex subtyping deferred" orig wl)
        else let t_base, _ = base_and_refinement env wl t1 in
             solve_t env ({problem with lhs=t_base; relation=EQ}) wl

      | Tm_refine _, _ ->
        let t2 = force_refinement <| base_and_refinement env wl t2 in
        solve_t env ({problem with rhs=t2}) wl

      | _, Tm_refine _ ->
        let t1 = force_refinement <| base_and_refinement env wl t1 in
        solve_t env ({problem with lhs=t1}) wl

      | Tm_match _, _
      | Tm_uinst _, _
      | Tm_name _, _
      | Tm_constant _, _
      | Tm_fvar _, _
      | Tm_app _, _
      | _, Tm_match _
      | _, Tm_uinst _
      | _, Tm_name _
      | _, Tm_constant _
      | _, Tm_fvar _
      | _, Tm_app _ ->
         let head1 = U.head_and_args t1 |> fst in
         let head2 = U.head_and_args t2 |> fst in
         if (Env.is_interpreted env head1
             || Env.is_interpreted env head2)   //we have something like (+ x1 x2) =?= (- y1 y2)
         && wl.smt_ok
         && problem.relation = EQ
         then let uv1 = Free.uvars t1 in
              let uv2 = Free.uvars t2 in
              if BU.set_is_empty uv1 && BU.set_is_empty uv2 //and we don't have any unification variables left to solve within the terms
              // TODO: GM: shouldn't we fail immediately if `eq_tm`
              // returns `NotEqual`?
              then let guard = if U.eq_tm t1 t2 = U.Equal
                               then None
                               else Some <| mk_eq2 env t1 t2 in
                   solve env (solve_prob orig guard [] wl)
              else rigid_rigid_delta env orig wl head1 head2 t1 t2
         else rigid_rigid_delta env orig wl head1 head2 t1 t2

      | Tm_ascribed(t1, _, _), _ ->
        solve_t' env ({problem with lhs=t1}) wl

      | _, Tm_ascribed(t2, _, _)->
        solve_t' env ({problem with rhs=t2}) wl

      | Tm_let _, _
      | Tm_meta _, _
      | Tm_delayed _, _
      | _, Tm_meta _
      | _, Tm_delayed _
      | _, Tm_let _ -> failwith (BU.format2 "Impossible: %s and %s" (Print.tag_of_term t1) (Print.tag_of_term t2))

      | _ -> giveup env "head tag mismatch" orig

and solve_c (env:Env.env) (problem:problem<comp,unit>) (wl:worklist) : solution =
    let c1 = problem.lhs in
    let c2 = problem.rhs in
    let orig = CProb problem in
    let sub_prob : term -> rel -> term -> string -> tprob =
        fun t1 rel t2 reason -> mk_problem (p_scope orig) orig t1 rel t2 None reason in

    let solve_eq c1_comp c2_comp =
        let _ = if Env.debug env <| Options.Other "EQ"
                then BU.print_string "solve_c is using an equality constraint\n" in
        let sub_probs = List.map2 (fun (a1, _) (a2, _) -> TProb<| sub_prob a1 EQ a2 "effect arg")
                        c1_comp.effect_args
                        c2_comp.effect_args in
        let guard = U.mk_conj_l (List.map (fun p -> p_guard p |> fst) sub_probs) in
        let wl = solve_prob orig (Some guard) [] wl in
        solve env (attempt sub_probs wl)
    in

    let solve_sub c1 edge c2 =
        let r = Env.get_range env in
        let lift_c1 () =
             let wp = match c1.effect_args with
                      | [(wp1,_)] -> wp1
                      | _ -> failwith (BU.format1 "Unexpected number of indices on a normalized effect (%s)" (Range.string_of_range (range_of_lid c1.effect_name))) in
             {
                comp_univs=c1.comp_univs;
                effect_name=c2.effect_name;
                result_typ=c1.result_typ;
                effect_args=[as_arg (edge.mlift.mlift_wp c1.result_typ wp)];
                flags=c1.flags
             }
        in
        if problem.relation = EQ
        then solve_eq (lift_c1 ()) c2
        else let is_null_wp_2 = c2.flags |> BU.for_some (function TOTAL | MLEFFECT | SOMETRIVIAL -> true | _ -> false) in
             let wpc1, wpc2 = match c1.effect_args, c2.effect_args with
              | (wp1, _)::_, (wp2, _)::_ -> wp1, wp2
              | _ ->
                raise (Error (BU.format2 "Got effects %s and %s, expected normalized effects"
                                          (Print.lid_to_string c1.effect_name)
                                          (Print.lid_to_string c2.effect_name), env.range))
             in
             if BU.physical_equality wpc1 wpc2
             then solve_t env (problem_using_guard orig c1.result_typ problem.relation c2.result_typ None "result type") wl
             else let c2_decl, qualifiers = must (Env.effect_decl_opt env c2.effect_name) in
                  if qualifiers |> List.contains Reifiable
                  then let c1_repr =
                           N.normalize [N.UnfoldUntil Delta_constant; N.WHNF] env
                                       (Env.reify_comp env (S.mk_Comp (lift_c1 ())) (env.universe_of env c1.result_typ))
                       in
                       let c2_repr =
                           N.normalize [N.UnfoldUntil Delta_constant; N.WHNF] env
                                       (Env.reify_comp env (S.mk_Comp c2) (env.universe_of env c2.result_typ))
                       in
                       let prob =
                           TProb (sub_prob c1_repr problem.relation c2_repr
                                      (BU.format2 "sub effect repr: %s <: %s"
                                                    (Print.term_to_string c1_repr)
                                                    (Print.term_to_string c2_repr)))
                       in
                       let wl = solve_prob orig (Some (p_guard prob |> fst)) [] wl in
                       solve env (attempt [prob] wl)
                  else
                      let g =
                         if env.lax then
                            U.t_true
                         else if is_null_wp_2
                         then let _ = if debug env <| Options.Other "Rel" then BU.print_string "Using trivial wp ... \n" in
                              mk (Tm_app(inst_effect_fun_with [env.universe_of env c1.result_typ] env c2_decl c2_decl.trivial,
                                        [as_arg c1.result_typ; as_arg <| edge.mlift.mlift_wp c1.result_typ wpc1]))
                                 (Some U.ktype0.n) r
                         else mk (Tm_app(inst_effect_fun_with [env.universe_of env c2.result_typ] env c2_decl c2_decl.stronger,
                                        [as_arg c2.result_typ; as_arg wpc2; as_arg <| edge.mlift.mlift_wp c1.result_typ wpc1]))
                                 (Some U.ktype0.n) r in
                      let base_prob = TProb <| sub_prob c1.result_typ problem.relation c2.result_typ "result type" in
                      let wl = solve_prob orig (Some <| U.mk_conj (p_guard base_prob |> fst) g) [] wl in
                      solve env (attempt [base_prob] wl)
    in

    if BU.physical_equality c1 c2
    then solve env (solve_prob orig None [] wl)
    else let _ = if debug env <| Options.Other "Rel"
                 then BU.print3 "solve_c %s %s %s\n"
                                    (Print.comp_to_string c1)
                                    (rel_to_string problem.relation)
                                    (Print.comp_to_string c2) in
         let c1, c2 = N.ghost_to_pure env c1, N.ghost_to_pure env c2 in
         match c1.n, c2.n with
               | GTotal (t1, _), Total (t2, _) when (U.non_informative t2) ->
                 solve_t env (problem_using_guard orig t1 problem.relation t2 None "result type") wl

               | GTotal _, Total _ ->
                 giveup env "incompatible monad ordering: GTot </: Tot"  orig

               | Total  (t1, _), Total  (t2, _)
               | GTotal (t1, _), GTotal (t2, _)
               | Total  (t1, _), GTotal (t2, _) -> //rigid-rigid 1
                 solve_t env (problem_using_guard orig t1 problem.relation t2 None "result type") wl

               | GTotal _, Comp _
               | Total _,  Comp _ ->
                 solve_c env ({problem with lhs=mk_Comp <| Env.comp_to_comp_typ env c1}) wl

               | Comp _, GTotal _
               | Comp _, Total _ ->
                 solve_c env ({problem with rhs=mk_Comp <| Env.comp_to_comp_typ env c2}) wl

               | Comp _, Comp _ ->
                 if (U.is_ml_comp c1 && U.is_ml_comp c2)
                    || (U.is_total_comp c1 && (U.is_total_comp c2 || U.is_ml_comp c2))
                 then solve_t env (problem_using_guard orig (U.comp_result c1) problem.relation (U.comp_result c2) None "result type") wl
                 else let c1_comp = Env.comp_to_comp_typ env c1 in
                      let c2_comp = Env.comp_to_comp_typ env c2 in
                      if problem.relation=EQ && lid_equals c1_comp.effect_name c2_comp.effect_name
                      then solve_eq c1_comp c2_comp
                      else
                         let c1 = Env.unfold_effect_abbrev env c1 in
                         let c2 = Env.unfold_effect_abbrev env c2 in
                         if debug env <| Options.Other "Rel" then BU.print2 "solve_c for %s and %s\n" (c1.effect_name.str) (c2.effect_name.str);
                         begin match Env.monad_leq env c1.effect_name c2.effect_name with
                           | None ->
                             if U.is_ghost_effect c1.effect_name
                             && U.is_pure_effect c2.effect_name
                             && U.non_informative (N.normalize [N.Eager_unfolding; N.UnfoldUntil Delta_constant] env c2.result_typ)
                             then let edge = {msource=c1.effect_name; mtarget=c2.effect_name; mlift=identity_mlift} in
                                  solve_sub c1 edge c2
                             else giveup env (BU.format2 "incompatible monad ordering: %s </: %s"
                                             (Print.lid_to_string c1.effect_name)
                                             (Print.lid_to_string c2.effect_name)) orig
                           | Some edge ->
                             solve_sub c1 edge c2
                         end

(* -------------------------------------------------------- *)
(* top-level interface                                      *)
(* -------------------------------------------------------- *)
let print_pending_implicits g = g.implicits |> List.map (fun (_, _, u, _, _, _) -> Print.uvar_to_string u) |> String.concat ", "

let ineqs_to_string ineqs =
    let vars =
        fst ineqs
        |> List.map Print.univ_to_string
        |> String.concat ", " in
    let ineqs =
        snd ineqs
        |> List.map (fun (u1, u2) ->
                BU.format2 "%s < %s"
                        (Print.univ_to_string u1)
                        (Print.univ_to_string u2))
        |> String.concat ", " in
    BU.format2 "Solving for {%s}; inequalities are {%s}"
                    vars ineqs

let guard_to_string (env:env) g =
  match g.guard_f, g.deferred, g.univ_ineqs with
    | Trivial, [], (_, []) -> "{}"
    | _ ->
      let form = match g.guard_f with
          | Trivial -> "trivial"
          | NonTrivial f ->
              if debug env <| Options.Other "Rel"
              || debug env <| Options.Other "Implicits"
              || debug env <| Options.Extreme
              then N.term_to_string env f
              else "non-trivial" in
      let carry = List.map (fun (_, x) -> prob_to_string env x) g.deferred |> String.concat ",\n" in
      let imps = print_pending_implicits g in
      BU.format4 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
        form carry (ineqs_to_string g.univ_ineqs) imps

let new_t_problem env lhs rel rhs elt loc =
 let reason = if debug env <| Options.Other "ExplainRel"
              then BU.format3 "Top-level:\n%s\n\t%s\n%s"
                        (N.term_to_string env lhs) (rel_to_string rel)
                        (N.term_to_string env rhs)
              else "TOP" in
 let p = new_problem env lhs rel rhs elt loc reason in
 p

let new_t_prob env t1 rel t2 =
 let x = S.new_bv (Some <| Env.get_range env) t1 in
 let env = Env.push_bv env x in
 let p = new_t_problem env t1 rel t2 (Some <| S.bv_to_name x) (Env.get_range env) in
 TProb p, x

let solve_and_commit env probs err =
  let probs = if (Options.eager_inference()) then {probs with defer_ok=false} else probs in
  let tx = Unionfind.new_transaction () in
  let sol = solve env probs in
  match sol with
    | Success (deferred) ->
      Unionfind.commit tx;
      Some deferred
    | Failed (d,s) ->
      Unionfind.rollback tx;
      if Env.debug env <| Options.Other "ExplainRel"
      then BU.print_string <| explain env d s;
      err (d,s)

let simplify_guard env g = match g.guard_f with
    | Trivial -> g
    | NonTrivial f ->
      if Env.debug env <| Options.Other "Simplification" then BU.print1 "Simplifying guard %s\n" (Print.term_to_string f);
      let f = N.normalize [N.Beta; N.Eager_unfolding; N.Simplify] env f in
      if Env.debug env <| Options.Other "Simplification" then BU.print1 "Simplified guard to %s\n" (Print.term_to_string f);
      let f = match (U.unmeta f).n with
        | Tm_fvar fv when S.fv_eq_lid fv Const.true_lid -> Trivial
        | _ -> NonTrivial f in
      {g with guard_f=f}

let with_guard env prob dopt = match dopt with
    | None -> None
    | Some d ->
      Some <| simplify_guard env ({guard_f=(p_guard prob |> fst |> NonTrivial); deferred=d; univ_ineqs=([], []); implicits=[]})

let with_guard_no_simp env prob dopt = match dopt with
    | None -> None
    | Some d ->
      Some ({guard_f=(p_guard prob |> fst |> NonTrivial); deferred=d; univ_ineqs=([], []); implicits=[]})

let try_teq smt_ok env t1 t2 : option<guard_t> =
 if debug env <| Options.Other "Rel"
 then BU.print2 "try_teq of %s and %s\n" (Print.term_to_string t1) (Print.term_to_string t2);
 let prob = TProb<| new_t_problem env t1 EQ t2 None (Env.get_range env) in
 let g = with_guard env prob <| solve_and_commit env (singleton' env prob smt_ok) (fun _ -> None) in
 g

let teq env t1 t2 : guard_t =
 match try_teq true env t1 t2 with
    | None -> raise (Error(Err.basic_type_error env None t2 t1, Env.get_range env))
    | Some g ->
      if debug env <| Options.Other "Rel"
      then BU.print3 "teq of %s and %s succeeded with guard %s\n"
                        (Print.term_to_string t1)
                        (Print.term_to_string t2)
                        (guard_to_string env g);
      g

let try_subtype' env t1 t2 smt_ok =
 if debug env <| Options.Other "Rel"
 then BU.print2 "try_subtype of %s and %s\n" (N.term_to_string env t1) (N.term_to_string env t2);
 let prob, x = new_t_prob env t1 SUB t2 in
 let g = with_guard env prob <| solve_and_commit env (singleton' env prob smt_ok) (fun _ -> None) in
 if debug env <| Options.Other "Rel"
    && BU.is_some g
 then BU.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                    (N.term_to_string env t1)
                    (N.term_to_string env t2)
                    (guard_to_string env (BU.must g));
 abstract_guard x g

let try_subtype env t1 t2 = try_subtype' env t1 t2 true

let subtype_fail env e t1 t2 =
    Errors.err (Env.get_range env) (Err.basic_type_error env (Some e) t2 t1)


let sub_comp env c1 c2 =
  if debug env <| Options.Other "Rel"
  then BU.print2 "sub_comp of %s and %s\n" (Print.comp_to_string c1) (Print.comp_to_string c2);
  let rel = if env.use_eq then EQ else SUB in
  let prob = CProb <| new_problem env c1 rel c2 None (Env.get_range env) "sub_comp" in
  with_guard env prob <| solve_and_commit env (singleton env prob)  (fun _ -> None)

let solve_universe_inequalities' tx env (variables, ineqs) =
   //variables: ?u1, ..., ?un are the universes of the inductive types we're trying to compute
   //ineqs: u1 < v1, ..., un < vn are inequality constraints gathered from checking the inductive definition
   //The basic idea is to collect all lowerbounds of each variable ?ui,
   //       excluding all of the variables themselves to avoid cycles
   //       and setting each ?ui to max(lowerbounds(?ui))
   //Then, we make a pass over all the inequalities again and check that they are all satisfied
   //This ensures, e.g., that we don't needlessly generalize types, avoid issues lik #806
   let fail u1 u2 =
        Unionfind.rollback tx;
        raise (Error (BU.format2 "Universe %s and %s are incompatible"
                                (Print.univ_to_string u1)
                                (Print.univ_to_string u2),
                      Env.get_range env))
   in
   let equiv v v' =
       match SS.compress_univ v, SS.compress_univ v' with
       | U_unif v0, U_unif v0' -> Unionfind.equivalent v0 v0'
       | _ -> false
   in
   let sols = variables |> List.collect (fun v ->
     match SS.compress_univ v with
     | U_unif _ -> //if it really is a variable, that try to solve it
         let lower_bounds_of_v = //lower bounds of v, excluding the other variables
           ineqs |> List.collect (fun (u, v') ->
             if equiv v v'
             then if variables |> BU.for_some (equiv u)
                  then []
                  else [u]
             else [])
         in
         let lb = N.normalize_universe env (U_max lower_bounds_of_v) in
         [(lb, v)]
     | _ ->
       //it may not actually be a variable in case the user provided an explicit universe annnotation
       //see, e.g., ulib/FStar.Universe.fst
      []) in
   //apply all the solutions
   let _ =
     let wl = {empty_worklist env with defer_ok=false} in
     sols |> List.map (fun (lb, v) ->
         //     printfn "Setting %s to its lower bound %s" (Print.univ_to_string v) (Print.univ_to_string lb);
         match solve_universe_eq (-1) wl lb v with
         | USolved wl -> ()
         | _ -> fail lb v)
   in
   //check that the solutions produced valid inequalities
   let rec check_ineq (u, v) : bool =
     let u = N.normalize_universe env u in
     let v = N.normalize_universe env v in
     match u, v with
     | U_zero, _ -> true
     | U_succ u0, U_succ v0 -> check_ineq (u0, v0)
     | U_name u0, U_name v0 -> Ident.ident_equals u0 v0
     | U_unif u0, U_unif v0 -> Unionfind.equivalent u0 v0
     | U_name _,  U_succ v0
     | U_unif _,  U_succ v0 -> check_ineq (u, v0)
     | U_max us,  _         -> us |> BU.for_all (fun u -> check_ineq (u, v))
     | _,         U_max vs  -> vs |> BU.for_some (fun v -> check_ineq (u, v))
     | _ -> false
   in
   if ineqs |> BU.for_all (fun (u, v) ->
        if check_ineq (u, v)
        then true
        else (if Env.debug env <| Options.Other "GenUniverses"
              then BU.print2 "%s </= %s" (Print.univ_to_string u) (Print.univ_to_string v);
              false))
   then ()
   else (if Env.debug env <| Options.Other "GenUniverses"
         then (BU.print1 "Partially solved inequality constraints are: %s\n" (ineqs_to_string (variables, ineqs));
               Unionfind.rollback tx;
               BU.print1 "Original solved inequality constraints are: %s\n" (ineqs_to_string (variables, ineqs)));
         raise (Error ("Failed to solve universe inequalities for inductives",
                      Env.get_range env)))

let solve_universe_inequalities env ineqs =
    let tx = Unionfind.new_transaction () in
    solve_universe_inequalities' tx env ineqs;
    Unionfind.commit tx

let rec solve_deferred_constraints env (g:guard_t) =
   let fail (d,s) =
      let msg = explain env d s in
      raise (Error(msg, p_loc d)) in
   let wl = wl_of_guard env g.deferred in
   if Env.debug env <| Options.Other "RelCheck"
   then BU.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"  (wl_to_string wl) (string_of_int (List.length g.implicits));
   let g = match solve_and_commit env wl fail with
    | Some [] -> {g with deferred=[]}
    | _ -> failwith "impossible: Unexpected deferred constraints remain" in
   solve_universe_inequalities env g.univ_ineqs;
   {g with univ_ineqs=([], [])}

//use_smt flag says whether to use the smt solver to discharge this guard
//if use_smt = true, this function NEVER returns None, the error might come from the smt solver though
//if use_smt = false, then None means could not discharge the guard without using smt
let discharge_guard' use_env_range_msg env (g:guard_t) (use_smt:bool) : option<guard_t> =
  let g = solve_deferred_constraints env g in
  let ret_g = {g with guard_f = Trivial} in
  if not (Env.should_verify env) then Some ret_g
  else
    match g.guard_f with
    | Trivial -> Some ret_g
    | NonTrivial vc ->
      if Env.debug env <| Options.Other "Norm"
      || Env.debug env <| Options.Other "SMTQuery"
      then Errors.diag (Env.get_range env)
                       (BU.format1 "Before normalization VC=\n%s\n" (Print.term_to_string vc));
      let vc = N.normalize [N.Eager_unfolding; N.Beta; N.Simplify] env vc in
      match check_trivial vc with
      | Trivial -> Some ret_g
      | NonTrivial vc ->
        if not use_smt then None
        else
          let _ =
            if Env.debug env <| Options.Other "Rel"
            then Errors.diag (Env.get_range env)
                             (BU.format1 "Checking VC=\n%s\n" (Print.term_to_string vc));
            let vcs =
                if Options.use_tactics()
                then env.solver.preprocess env vc
                else [env,vc] in
            vcs |> List.iter (fun (env, goal) -> env.solver.solve use_env_range_msg env goal)
          in
          Some ret_g

let discharge_guard env g =
  match discharge_guard' None env g true with
  | Some g -> g
  | None   -> failwith "Impossible, with use_smt = true, discharge_guard' should never have returned None"

let resolve_implicits g =
  let unresolved u = match Unionfind.find u with
    | Uvar -> true
    | _ -> false in
  let rec until_fixpoint (acc: Env.implicits * bool) (implicits:Env.implicits) : Env.implicits =
    let out, changed = acc in
    match implicits with
        | [] -> if not changed then out else until_fixpoint ([], false) out
        | hd::tl ->
          let (_, env, u, tm, k, r) = hd in
          if unresolved u
          then until_fixpoint (hd::out, changed) tl
          else let env = Env.set_expected_typ env k in
               let tm = N.normalize [N.Beta] env tm in
               if Env.debug env <| Options.Other "RelCheck"
               then BU.print3 "Checking uvar %s resolved to %s at type %s\n"
                                 (Print.uvar_to_string u) (Print.term_to_string tm) (Print.term_to_string k);
               let _, _, g = env.type_of ({env with use_bv_sorts=true}) tm in
               let g = if env.is_pattern
                       then {g with guard_f=Trivial} //if we're checking a pattern sub-term, then discard its logical payload
                       else g in
               let g' =
                 match discharge_guard' (Some (fun () -> Print.term_to_string tm)) env g true with
                 | Some g -> g
                 | None   -> failwith "Impossible, with use_smt = true, discharge_guard' should never have returned None"
               in
               until_fixpoint (g'.implicits@out, true) tl in
  {g with implicits=until_fixpoint ([], false) g.implicits}

let force_trivial_guard env g =
    let g = solve_deferred_constraints env g |> resolve_implicits in
    match g.implicits with
        | [] -> ignore <| discharge_guard env g
        | (reason,_,_,e,t,r)::_ ->
           Errors.err r (BU.format3 "Failed to resolve implicit argument of type '%s' introduced in %s because %s"
                                    (Print.term_to_string t)
                                    (Print.term_to_string e)
                                    reason)

let universe_inequality (u1:universe) (u2:universe) : guard_t =
    //Printf.printf "Universe inequality %s <= %s\n" (Print.univ_to_string u1) (Print.univ_to_string u2);
    {trivial_guard with univ_ineqs=([], [u1,u2])}

let teq_nosmt (env:env) (t1:typ) (t2:typ) :bool =
  match try_teq false env t1 t2 with
  | None -> false
  | Some g ->
    match discharge_guard' None env g false with
    | Some _ -> true
    | None   -> false


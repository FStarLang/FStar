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

open FStar
open FStar.Util
open FStar.TypeChecker
open FStar.Syntax
open FStar.TypeChecker.Env
open FStar.Syntax.Syntax
open FStar.Syntax.Subst
open FStar.Ident
module U = FStar.Syntax.Util
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module N = FStar.TypeChecker.Normalize

(* --------------------------------------------------------- *)
(* <new_uvar> Generating new unification variables/patterns  *)
(* --------------------------------------------------------- *)
let new_uvar r binders k =
  let binders = binders |> List.filter (fun x -> is_null_binder x |> not) in
  let uv = Unionfind.fresh Uvar in
  match binders with
    | [] ->
      let uv = mk (Tm_uvar(uv,k)) None r in
      uv, uv
    | _ ->
      let args = Util.args_of_non_null_binders binders in
      let k' = U.arrow binders (mk_Total k) in
      let uv = mk (Tm_uvar(uv,k')) None r in
      mk (Tm_app(uv, args)) None r, uv
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
    scope: binders;
    reason: list<string>;             //why we generated this problem, for error reporting
    loc: Range.range;                 //and the source location where this arose
    rank: option<int>;
}
type problem_t<'a,'b> = problem<'a,'b>
type tprob = problem<typ, term>
type cprob = problem<comp, unit>
type prob =
  | TProb of problem<typ, term>
  | CProb of problem<comp,unit>

type probs = list<prob>

(* Instantiation of unification variables *)
type uvi = (uvar * typ) * typ 

(* The set of problems currently being addressed *)
type worklist = {
    attempting:  probs;
    wl_deferred: list<(int * string * prob)>;  //flex-flex cases, non patterns, and subtyping constraints involving a unification variable,
    subst:       list<uvi>;                    //the partial solution derived so far
    ctr:         int;                          //a counter incremented each time we extend subst, used to detect if we've made progress
    defer_ok:    bool;                         //whether or not carrying constraints is ok---at the top-level, this flag is false
    smt_ok:      bool;                         //whether or not falling back to the SMT solver is permitted
    tcenv:       Env.env;
}

(* Types used in the output of the solver *)
type deferred = list<(string * prob)>
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
  | TProb p ->
    Util.format "\t%s (%s) \n\t\t%s(%s)\n\t%s (%s) (guard %s)"
        [(N.term_to_string env p.lhs);
         (Print.tag_of_term p.lhs);
         (rel_to_string p.relation);
         (p.reason |> List.hd);
         (N.term_to_string env p.rhs);
         (Print.tag_of_term p.rhs);
         (N.term_to_string env (fst p.logical_guard))]
  | CProb p -> Util.format3 "\t%s \n\t\t%s\n\t%s" (N.comp_to_string env p.lhs) (rel_to_string p.relation) (N.comp_to_string env p.rhs)

let uvi_to_string env ((u,_), t) =
  let x = if !Options.hide_uvar_nums then "?" else Unionfind.uvar_id u |> string_of_int in
  Util.format2 "UT %s %s" x (N.term_to_string env t)

let names_to_string nms = Util.set_elements nms |> List.map Print.bv_to_string |> String.concat ", "
let args_to_string args = args |> List.map (fun (x, _) -> Print.term_to_string x) |> String.concat " "

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
    | TProb p -> maybe_invert p |> TProb
    | CProb p -> maybe_invert p |> CProb
let vary_rel rel = function
    | INVARIANT -> EQ
    | CONTRAVARIANT -> invert_rel rel
    | COVARIANT -> rel
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

let mk_problem scope orig lhs rel rhs elt reason = {
     lhs=lhs;
     relation=rel;
     rhs=rhs;
     element=elt;
     logical_guard=new_uvar (p_loc orig) scope U.ktype0; //logical guards are always squashed?
     reason=reason::p_reason orig;
     loc=p_loc orig;
     rank=None;
     scope=scope;
}
let new_problem env lhs rel rhs elt loc reason =
  let scope = Env.binders env in 
   {
    lhs=lhs;
    relation=rel;
    rhs=rhs;
    element=elt;
    logical_guard=new_uvar (Env.get_range env) scope U.ktype0; //logical guards are always squashed?
    reason=[reason];
    loc=loc;
    rank=None;
    scope=scope;
   }
let problem_using_guard orig lhs rel rhs elt reason = {
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
let guard_on_element problem x phi =
    match problem.element with
        | None ->   U.mk_forall x phi
        | Some e -> Subst.subst [NT(x,e)] phi

let solve_prob' resolve_ok prob logical_guard uvis wl =
    let phi = match logical_guard with
      | None -> Util.t_true
      | Some phi -> phi in
    let _, uv = p_guard prob in
    let _ = match (compress uv).n with
        | Tm_uvar(uvar, k) ->
          let bs, _ = U.arrow_formals k in
          let phi   = U.abs bs phi in         //TODO: CHECK THIS! is it really going close over the free variables of phi?
          Util.unchecked_unify uvar phi
        | _ -> if not resolve_ok then failwith "Impossible: this instance has already been assigned a solution" in
    match uvis with
        | [] -> wl
        | _ ->
        if Env.debug wl.tcenv <| Options.Other "Rel"
        then Util.fprint1 "Extending solution: %s\n" (List.map (uvi_to_string wl.tcenv) uvis |> String.concat ", ");
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
    tcenv=env;
    defer_ok=true;
    smt_ok=true
}
let singleton env prob     = {empty_worklist env with attempting=[prob]}
let wl_of_guard env g      = {empty_worklist env with defer_ok=false; attempting=List.map snd g}
let defer reason prob wl   = {wl with wl_deferred=(wl.ctr, reason, prob)::wl.wl_deferred}
let attempt probs wl       = {wl with attempting=probs@wl.attempting}

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
let commit env uvis = uvis |> List.iter (fun ((u, _), t) -> Util.unchecked_unify u t)
let find_uvar uv s = Util.find_map s (fun ((u,_), t) -> if Unionfind.equivalent uv u then Some t else None)
(* ------------------------------------------------*)
(* </uvi ops>                                      *)
(* ------------------------------------------------*)


(* ------------------------------------------------*)
(* <normalization>                                *)
(* ------------------------------------------------*)
let simplify_formula env f = N.normalize [N.Beta; N.Simplify] env f
let norm_arg env t = N.normalize [N.Beta] env (fst t), snd t
let whnf env t = compress (N.whnf env t)
let sn env t = compress (N.normalize [N.Beta; N.Eta] env t)
let sn_binders env (binders:binders) =
    binders |> List.map (fun (x, imp) -> {x with sort=N.normalize [N.Beta] env x.sort}, imp)

let rec compress env wl t =
    let t = whnf env (Util.unmeta t) in
    match t.n with
        | Tm_uvar (uv, _) ->
           (match find_uvar uv wl.subst with
                | None -> t
                | Some t -> compress env wl t)
        | Tm_app({n=Tm_uvar(uv, _)}, args) ->
            (match find_uvar uv wl.subst with
                | Some t' ->
                  let t = mk (Tm_app(t', args)) None t.pos in
                  compress env wl t
                | _ -> t)
        | _ -> t

let normalize_refinement env wl t0 = N.normalize_refinement env (compress env wl t0)

let base_and_refinement env wl t1 =
   let rec aux norm t1 =
        match t1.n with
        | Tm_refine(x, phi) ->
            if norm
            then (x.sort, Some(x, phi))
            else begin match normalize_refinement env wl t1 with
                | {n=Tm_refine(x, phi)} -> (x.sort, Some(x, phi))
                | tt -> failwith (Util.format2 "impossible: Got %s ... %s\n" (Print.term_to_string tt) (Print.tag_of_term tt))
            end

        | Tm_fvar _ 
        | Tm_app _ ->
            if norm
            then (t1, None)
            else let t2', refinement = aux true (normalize_refinement env wl t1) in
                 begin match refinement with
                    | None -> t1, None (* no refinement found ... so revert to the original type, without expanding defs *)
                    | _ -> t2', refinement
                 end

        | Tm_type _
        | Tm_constant _
        | Tm_name _
        | Tm_bvar _
        | Tm_arrow _
        | Tm_abs _
        | Tm_uvar _ -> (t1, None)

        | Tm_uinst _
        | Tm_let _
        | Tm_match _ -> failwith "Unhandled cases!"

        | Tm_meta _
        | Tm_ascribed _  //NS: Why are the two previous cases excluded?
        | Tm_delayed _
        | Tm_unknown -> failwith (Util.format2 "impossible (outer): Got %s ... %s\n" (Print.term_to_string t1) (Print.tag_of_term t1)) in
   aux false (compress env wl t1)

let unrefine env t = base_and_refinement env (empty_worklist env) t |> fst

let trivial_refinement t = S.null_bv t, Util.t_true

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
(* <variable ops> common ops on variables           *)
(* ------------------------------------------------ *)
let rec occurs (wl:worklist) (uk:(uvar * 'b)) (t:typ) =
    let uvs = Free.uvars t in
    uvs |> Util.set_elements |> Util.for_some (fun (uv, _) ->
        match find_uvar uv wl.subst with
            | None -> Unionfind.equivalent uv (fst uk)
            | Some t ->
               let t = match Subst.compress t with
                        | {n=Tm_abs(_, t)} -> t
                        | t -> t in
              occurs wl uk t)

let occurs_check env wl uk t =
    let occurs_ok = not (occurs wl uk t) in
    let msg =
        if occurs_ok then None
        else Some (Util.format3 "occurs-check failed (%s occurs in %s) (with substitution %s)"
                        (Print.uvar_to_string (fst uk))
                        (Print.term_to_string t)
                        (wl.subst |> List.map (uvi_to_string env) |> String.concat ", ")) in
    occurs_ok, msg

let occurs_and_freevars_check env wl uk fvs t =
    let fvs_t = Free.names t in
    let occurs_ok, msg = occurs_check env wl uk t in
    (occurs_ok, Util.set_is_subset_of fvs_t fvs, (msg, fvs, fvs_t))

let intersect_vars v1 v2 =
    let fvs1 = Free.names_of_binders v1 in
    let fvs2 = Free.names_of_binders v2 in
    Util.set_intersect fvs1 fvs2 |> Util.set_elements |> List.map mk_binder

let binders_eq v1 v2 =
  List.length v1 = List.length v2
  && List.forall2 (fun (a, _) (b, _) -> S.bv_eq a b) v1 v2

let pat_var_opt env seen arg =
   let hd = norm_arg env arg in
   match (fst hd).n with
    | Tm_name a ->
        if seen |> Util.for_some (fun (b, _) -> bv_eq a b)
        then None
        else Some (a, snd hd)

    | _ -> None

let rec pat_vars env seen args : option<binders> = match args with
    | [] -> Some (List.rev seen)
    | hd::rest ->
        begin match pat_var_opt env seen hd with
            | None -> if Env.debug env <| Options.Other "Rel" then Util.fprint1 "Not a pattern: %s\n" (Print.term_to_string <| fst hd); None //not a pattern
            | Some x -> pat_vars env (x::seen) rest
        end

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
  | MisMatch
  | HeadMatch
  | FullMatch

let head_match = function
    | MisMatch -> MisMatch
    | _ -> HeadMatch

let rec head_matches t1 t2 : match_result =
  match (Util.unmeta t1).n, (Util.unmeta t2).n with
    | Tm_name x, Tm_name y -> if S.bv_eq x y then FullMatch else MisMatch
    | Tm_fvar f, Tm_fvar g -> if S.fv_eq f g then FullMatch else MisMatch
    | Tm_constant c, Tm_constant d -> if c=d then FullMatch else MisMatch
    | Tm_uvar (uv, _),  Tm_uvar (uv', _) -> if Unionfind.equivalent uv uv' then FullMatch else MisMatch

    | Tm_refine(x, _), Tm_refine(y, _) -> head_matches x.sort y.sort |> head_match

    | Tm_refine(x, _), _  -> head_matches x.sort t2 |> head_match
    | _, Tm_refine(x, _)  -> head_matches t1 x.sort |> head_match

    | Tm_arrow _, Tm_arrow _ -> HeadMatch

    | Tm_app(head, _), Tm_app(head', _) -> head_matches head head'
    | Tm_app(head, _), _ -> head_matches head t2
    | _, Tm_app(head, _) -> head_matches t1 head

    | Tm_abs _, _
    | _, Tm_abs _ -> HeadMatch

    | _ -> MisMatch

(* Does t1 match t2, after some delta steps? *)
let head_matches_delta env wl t1 t2 : (match_result * option<(typ*typ)>) =
    let success d r t1 t2 = (r, (if d then Some(t1, t2) else None)) in
    let fail () = (MisMatch, None) in
    let rec aux d t1 t2 =
        match head_matches t1 t2 with
            | MisMatch ->
                if d then fail() //already delta normal
                else let t1 = normalize_refinement env wl t1 in
                     let t2 = normalize_refinement env wl t2 in
                     aux true t1 t2
            | r -> success d r t1 t2 in
    aux false t1 t2

type tc =
 | T of term
 | C of comp
type tcs = list<tc>

let rec decompose env t : (list<tc> -> term) * (term -> bool) * list<(option<binder> * variance * tc)> =
    let t = Util.unmeta t in
    let matches t' = head_matches t t' <> MisMatch in
    match t.n with
        | Tm_app(hd, args) -> (* easy case: it's already in the form we want *)
            let rebuild args' =
            let args = List.map2 (fun x y -> match x, y with
                | (_, imp), T t -> t, imp
                | _ -> failwith "Bad reconstruction") args args' in
            mk (Tm_app(hd, args)) None t.pos in

            let tcs = //each argument in order, with empty binders
            args |> List.map (fun (t, _) -> None, INVARIANT, T t) in

            rebuild, matches, tcs

        | Tm_arrow(bs, c) ->
            let fail () = failwith "Bad reconstruction" in
            let bs, c = Subst.open_comp bs c in

            let rebuild tcs =
                let rec aux out (bs:binders) tcs = match bs, tcs with
                    | (x, imp)::bs, T t::tcs -> aux (({x with sort=t},imp)::out) bs tcs
                    | [], [C c] -> U.arrow (List.rev out) c
                    | _ -> failwith "Bad reconstruction" in
                aux [] bs tcs in

            let rec decompose out = function
                | [] -> List.rev ((None, COVARIANT, C c)::out)
                | hd::rest ->
                  let bopt = if is_null_binder hd then None else Some hd in
                  decompose ((bopt, CONTRAVARIANT, T ((fst hd).sort))::out) rest in

            rebuild, 
            matches, 
            decompose [] bs

        | _ ->
          let rebuild = function
            | [] -> t
            | _ -> failwith "Bad reconstruction" in

          rebuild, (fun t -> true), []

let un_T = function
    | T t -> t
    | _ -> failwith "Impossible"

let arg_of_tc = function
    | T t -> arg t
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
        | _, variance, T ti ->
            let k = match !ti.tk with
                | Some k -> mk k None ti.pos
                | None -> Recheck.check ti in
            let gi_xs, gi = new_uvar r scope k in
            let gi_ps = match args with 
                | [] -> gi
                | _ -> mk (Tm_app(gi, args)) None r in
            T gi_xs,
            TProb <| mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm"

        | _, _, C _ -> failwith "impos" in

    let rec aux scope args qs : (list<prob> * list<tc> * formula) =
        match qs with
            | [] -> [], [], Util.t_true
            | q::qs ->
                let tc, probs = match q with
                     | bopt, variance, C ({n=Total ti}) ->
                       begin match sub_prob scope args (bopt, variance, T ti) with
                            | T gi_xs, prob -> C <| mk_Total gi_xs, [prob]
                            | _ -> failwith "impossible"
                       end

                    |_, _, C ({n=Comp c}) ->
                       let components = c.effect_args |> List.map (fun t -> (None, INVARIANT, T (fst t))) in
                       let components = (None, COVARIANT, T c.result_typ)::components in
                       let tcs, sub_probs = List.map (sub_prob scope args) components |> List.unzip in
                       let gi_xs = mk_Comp <| {
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
                    | None -> Util.mk_conj_l (f:: (probs |> List.map (fun prob -> p_guard prob |> fst)))
                    | Some b -> Util.mk_conj_l (U.mk_forall (fst b) f :: (probs |> List.map (fun prob -> p_guard prob |> fst))) in

                probs@sub_probs, tc::tcs, f in

   aux scope ps qs

(* ------------------------------------------------ *)
(* </decomposition>                                 *)
(* ------------------------------------------------ *)

(* ---------------------------------------------------------------------- *)
(* <eq_args> Special case of deciding syntactic equality, an optimization *)
(* ---------------------------------------------------------------------- *)
let rec eq_tm (t1:typ) (t2:typ) =
    let t1 = SS.compress t1 in
    let t2 = SS.compress t2 in
    match t1.n, t2.n with
        | Tm_name a, Tm_name b -> S.bv_eq a b
        | Tm_fvar f, Tm_fvar g -> S.fv_eq f g
        | Tm_constant c, Tm_constant d -> c=d
        | Tm_uvar (u1, _), Tm_uvar (u2, _) -> Unionfind.equivalent u1 u2
        | Tm_app (h1, args1), Tm_app(h2, args2) ->
          eq_tm h1 h2 && eq_args args1 args2
        | _ -> false

and eq_args (a1:args) (a2:args) : bool =
    List.length a1 = List.length a2
    && List.forall2 (fun (a1, _) (a2, _) -> eq_tm a1 a1) a1 a2
    
(* ------------------------------------------------ *)
(* <solver> The main solving algorithm              *)
(* ------------------------------------------------ *)
type flex_t = (term * uvar * typ * args)
type im_or_proj_t = ((uvar * typ) * list<arg> * binders * ((list<tc> -> typ) * (typ -> bool) * list<(option<binder> * variance * tc)>))

let rigid_rigid       = 0
let flex_rigid_eq     = 1
let flex_refine_inner = 2
let flex_refine       = 3
let flex_rigid        = 4
let rigid_flex        = 5
let refine_flex       = 6
let flex_flex         = 7
let compress_tprob wl p = {p with lhs=compress   wl.tcenv wl p.lhs; rhs=compress   wl.tcenv wl p.rhs}
let compress_prob wl p = match p with
    | TProb p -> compress_tprob wl p |> TProb
    | CProb _ -> p

let rank wl prob =
   let prob = compress_prob wl prob |> maybe_invert_p in
   match prob with
    | TProb tp ->
      let lh, _ = Util.head_and_args tp.lhs in
      let rh, _ = Util.head_and_args tp.rhs in
      let rank, tp = begin match lh.n, rh.n with
        | Tm_uvar _, Tm_uvar _ -> flex_flex, tp

        | Tm_uvar _, _
        | _, Tm_uvar _ when (tp.relation=EQ) -> flex_rigid_eq, tp

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
    if Env.debug env <| Options.Other "Rel"
    then Util.fprint1 "Trying to solve by joining refinements:%s\n" (prob_to_string env (TProb tp));
    let u, args = Util.head_and_args tp.lhs in
    let ok, head_match, partial_match, fallback, failed_match = 0,1,2,3,4 in
    let max i j = if i < j then j else i in

    let base_types_match t1 t2 : option<list<prob>> =
        let h1, args1 = Util.head_and_args t1 in
        let h2, _ = Util.head_and_args t2 in
        match h1.n, h2.n with
        | Tm_fvar tc1, Tm_fvar tc2 ->
          if S.fv_eq tc1 tc2
          then (if List.length args1 = 0
                then Some []
                else Some [TProb <| new_problem env t1 EQ t2 None t1.pos "joining refinements"])
          else None

        | Tm_name a, Tm_name b ->
          if S.bv_eq a b
          then Some []
          else None

        | _ -> None in

    let conjoin t1 t2 = match t1.n, t2.n with
        | Tm_refine(x, phi1), Tm_refine(y, phi2) ->
          let m = base_types_match x.sort y.sort in
          begin match m with
            | None -> None
            | Some m ->
              let x = freshen_bv x in 
              let subst = [DB(0, S.bv_to_name x)] in
              let phi1 = SS.subst subst phi1 in
              let phi2 = SS.subst subst phi2 in
              Some (U.refine x (Util.mk_conj phi1 phi2), m)
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
                      let u', _ = Util.head_and_args tp.lhs in
                      begin match (compress env wl u').n with
                        | Tm_uvar(uv', _) -> Unionfind.equivalent uv uv'
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
              if Env.debug env <| Options.Other "Rel"
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

and solve (env:Env.env) (probs:worklist) : solution =
//    printfn "Solving TODO:\n%s;;" (List.map prob_to_string probs.attempting |> String.concat "\n\t");
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
              else solve_t' env (maybe_invert tp) probs
         end

       | None, _, _ ->
         match probs.wl_deferred with
            | [] -> 
              Success (probs.subst, []) //Yay ... done!

            | _ ->
              let attempt, rest = probs.wl_deferred |> List.partition (fun (c, _, _) -> c < probs.ctr) in
              match attempt with
                 | [] -> //can't solve yet; defer the rest
                   Success(probs.subst, List.map (fun (_, x, y) -> (x, y)) probs.wl_deferred)

                 | _ -> 
                   solve env ({probs with attempting=attempt |> List.map (fun (_, _, y) -> y); wl_deferred=rest})


and solve_binders (env:Env.env) (bs1:binders) (bs2:binders) (orig:prob) (wl:worklist)
                  (rhs:binders -> Env.env -> list<subst_elt> -> prob) : solution =

   let rec aux scope env subst (xs:binders) (ys:binders) : either<(probs * formula), string> =
        match xs, ys with
            | [], [] ->
              let rhs_prob = rhs (List.rev scope) env subst in
              let formula = p_guard rhs_prob |> fst in
              Inl ([rhs_prob], formula)

            | (hd1, imp)::xs, (hd2, imp')::ys when imp=imp' ->
               let hd1 = {hd1 with sort=Subst.subst subst hd1.sort} in //open both binders
               let hd2 = {hd2 with sort=Subst.subst subst hd2.sort} in 
               let prob = TProb <| mk_problem ((hd1,imp)::scope) orig hd1.sort (invert_rel <| p_rel orig) hd2.sort None "Formal parameter" in
               let hd1 = freshen_bv hd1 in
               let subst = DB(0, S.bv_to_name hd1)::subst in  //extend the substitution
               let env = Env.push_local_binding env (Env.Binding_var(hd1, ([],hd1.sort))) in
               begin match aux ((hd1,imp)::scope) env subst xs ys with
                 | Inl (sub_probs, phi) ->
                   let phi = Util.mk_conj (p_guard prob |> fst) (U.close_forall [(hd2,imp)] phi) in
                   Inl (prob::sub_probs, phi)

                 | fail -> fail
               end

           | _ -> Inr "arity mismatch" in

   let scope = Env.bound_vars env |> List.map S.mk_binder in
   match aux scope env [] bs1 bs2 with
    | Inr msg -> giveup env msg orig
    | Inl (sub_probs, phi) ->
      let wl = solve_prob orig (Some phi) [] wl in
      solve env (attempt sub_probs wl)

and solve_t (env:Env.env) (problem:tprob) (wl:worklist) : solution =
    solve_t' env (compress_tprob wl problem) wl

and solve_t' (env:Env.env) (problem:tprob) (wl:worklist) : solution =
    let giveup_or_defer orig msg =
        if wl.defer_ok
        then begin
            if Env.debug env <| Options.Other "Rel"
            then Util.fprint2 "\n\t\tDeferring %s\n\t\tBecause %s\n" (prob_to_string env orig) msg;
            solve env (defer msg orig wl)
        end
        else giveup env msg orig in

    (* <imitate> used in flex-rigid *)
    let imitate orig (env:Env.env) (wl:worklist) (p:im_or_proj_t) : solution =
        let ((u,k), ps, xs, (h, _, qs)) = p in
        let xs = sn_binders env xs in
        //U p1..pn REL h q1..qm
        //if h is not a free variable
        //extend_subst: (U -> \x1..xn. h (G1(x1..xn), ..., Gm(x1..xm)))
        //sub-problems: Gi(p1..pn) REL' qi, where REL' = vary_rel REL (variance h i)
        let r = Env.get_range env in
        let sub_probs, gs_xs, formula = imitation_sub_probs orig env xs ps qs in
        let im = U.abs xs (h gs_xs) in
        if Env.debug env <| Options.Other "Rel"
        then Util.fprint4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n"
            (Print.term_to_string im) (Print.tag_of_term im)
            (List.map (prob_to_string env) sub_probs |> String.concat ", ")
            (Normalize.term_to_string env formula);
        let wl = solve_prob orig (Some formula) [((u,k), im)] wl in
        solve env (attempt sub_probs wl) in
    (* </imitate> *)

    (* <project> used in flex_rigid *)
    let project orig (env:Env.env) (wl:worklist) (i:int) (p:im_or_proj_t) : option<solution> =
        let (u, ps, xs, (h, matches, qs)) = p in
        //U p1..pn REL h q1..qm
        //extend subst: U -> \x1..xn. xi(G1(x1...xn) ... Gk(x1..xm)) ... where k is the arity of ti
        //sub-problems: pi(G1(p1..pn)..Gk(p1..pn)) REL h q1..qm
        let r = Env.get_range env in
        let pi, _ = List.nth ps i in
        let xi, _ = List.nth xs i in

        let rec gs k =
            let bs, k = Util.arrow_formals k in
            let rec aux subst bs = match bs with
                | [] -> [], []
                | (a, _)::tl ->
                    let k_a = SS.subst subst a.sort in
                    let gi_xs, gi = new_uvar r xs k_a in
                    let gi_xs = Normalize.eta_expand env gi_xs in
                    let gi_ps = mk_Tm_app gi ps (Some k_a.n) r in
                    let subst = if S.is_null_bv a then subst else NT(a, gi_xs)::subst in
                    let gi_xs', gi_ps' = aux subst tl in
                    arg gi_xs::gi_xs', arg gi_ps::gi_ps' in
              aux [] bs in

        if not <| matches pi
        then None
        else let g_xs, _ = gs xi.sort in
             let xi = S.bv_to_name xi in
             let proj = U.abs xs (S.mk_Tm_app xi g_xs None r) in
             let sub = TProb <| mk_problem (p_scope orig) orig (S.mk_Tm_app proj ps None r) (p_rel orig) (h <| List.map (fun (_, _, y) -> y) qs) None "projection" in
             if debug env <| Options.Other "Rel" then Util.fprint2 "Projecting %s\n\tsubprob=%s\n" (Print.term_to_string proj) (prob_to_string env sub);
             let wl = solve_prob orig (Some (fst <| p_guard sub)) [(u, proj)] wl in
             Some <| solve env (attempt [sub] wl) in
    (* </project_t> *)

    (* <flex-rigid> *)
    let solve_t_flex_rigid orig (lhs:(flex_t * option<binders>)) (t2:typ) (wl:worklist) =
        let (t1, uv, k, args_lhs), maybe_pat_vars = lhs in
        let subterms ps =
            let xs = Util.arrow_formals k |> fst in
            (uv,k), ps, xs, decompose env t2 in

        let rec imitate_or_project n st i =
            if i >= n then giveup env "flex-rigid case failed all backtracking attempts" orig
            else if i = -1
            then match imitate orig env wl st with
                    | Failed _ -> imitate_or_project n st (i + 1) //backtracking point
                    | sol -> sol
            else match project orig env wl i st with
                    | None
                    | Some (Failed _) -> imitate_or_project n st (i + 1) //backtracking point
                    | Some sol -> sol in

        let check_head fvs1 t2 =
            let hd, _ = Util.head_and_args t2 in
            match hd.n with
                | Tm_arrow _
                | Tm_constant _
                | Tm_abs _  -> true
                | _ ->
                    let fvs_hd = Free.names hd in
                    if Util.set_is_subset_of fvs_hd fvs1
                    then true
                    else (if Env.debug env <| Options.Other "Rel" 
                          then Util.fprint1 "Free variables are %s" (names_to_string fvs_hd); false) in

        let imitate_ok t2 = (* -1 means begin by imitating *)
            let fvs_hd = Util.head_and_args t2 |> fst |> Free.names in
            if Util.set_is_empty fvs_hd
            then -1 (* yes, start by imitating *)
            else 0 (* no, start by projecting *) in

        match maybe_pat_vars with
          | Some vars ->
            let t1 = sn env t1 in
            let t2 = sn env t2 in
            let fvs1 = Free.names t1 in
            let fvs2 = Free.names t2 in
            let occurs_ok, msg = occurs_check env wl (uv,k) t2 in
            if not occurs_ok
            then giveup_or_defer orig ("occurs-check failed: " ^ (Option.get msg))
            else if Util.set_is_subset_of fvs2 fvs1
            then (if Util.is_function_typ t2 && p_rel orig <> EQ //function types have structural subtyping and have to be imitated
                  then imitate orig env wl (subterms args_lhs)
                  else //fast solution, pattern equality
                    let _  = if debug env <| Options.Other "Rel"
                             then Util.fprint3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" 
                                    (Print.term_to_string t1) 
                                    (names_to_string fvs1) 
                                    (names_to_string fvs2) in
                    let sol = match vars with
                        | [] -> t2
                        | _ -> U.abs (sn_binders env vars) t2 in
                    let wl = solve_prob orig None [((uv,k), sol)] wl in
                    solve env wl)
            else if wl.defer_ok
            then solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl)
            else if check_head fvs1 t2
            then let _ = if debug env <| Options.Other "Rel"
                            then Util.fprint3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                            (Print.term_to_string t1) 
                                            (names_to_string fvs1)
                                            (names_to_string fvs2) in
                    imitate_or_project (List.length args_lhs) (subterms args_lhs) (-1)
            else giveup env "free-variable check failed on a non-redex" orig

          | None ->
                if wl.defer_ok
                then solve env (defer "not a pattern" orig wl)
                else if check_head (Free.names t1) t2
                then let im_ok = imitate_ok t2 in
                     let _ = if debug env <| Options.Other "Rel"
                             then Util.fprint2 "Not a pattern (%s) ... %s\n" 
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
            let rec aux binders ys args = match args with
                | [] ->
                    let ys = List.rev ys in
                    let binders = List.rev binders in
                    let kk = Recheck.check t in
                    let t', _ = new_uvar t.pos ys kk in
                    let u1_ys, u1, k1, _ = destruct_flex_t t' in
                    let sol = ((u,k), U.abs binders u1_ys) in
                    sol, (t', u, k1, ys)

                | hd::tl ->
                  let new_binder (hd, _) = Recheck.check hd |> S.gen_bv "x" (Some hd.pos) |> S.mk_binder in

                  let binder, ys = match pat_var_opt env ys hd with
                    | None -> new_binder hd, ys

                    | Some y ->
                      begin match xs_opt with
                        | None -> y, y::ys
                        | Some xs ->
                          if xs |> Util.for_some (fun (x, _) -> S.bv_eq x (fst y))
                          then y, y::ys  //this is a variable in the intersection with xs
                          else new_binder hd, ys

                      end in


                    aux (binder::binders) ys tl in

           aux [] [] args in


        let solve_both_pats wl (u1, k1, xs) (u2, k2, ys) k r =
            if Unionfind.equivalent u1 u2 
            && binders_eq xs ys
            then solve env (solve_prob orig None [] wl)
            else //U1 xs =?= U2 ys
                 //zs = xs intersect ys, U fresh
                 //U1 = \x1 x2. U zs
                 //U2 = \y1 y2 y3. U zs
                let xs = sn_binders env xs in
                let ys = sn_binders env ys in
                let zs = intersect_vars xs ys in
                let u_zs, _ = new_uvar r zs k in
                let sub1 = U.abs xs u_zs in
                let occurs_ok, msg = occurs_check env wl (u1,k1) sub1 in
                if not occurs_ok
                then giveup_or_defer orig "flex-flex: failed occcurs check"
                else let sol1 = ((u1, k1), sub1) in
                     if Unionfind.equivalent u1 u2
                     then let wl = solve_prob orig None [sol1] wl in
                          solve env wl
                     else let sub2 = U.abs ys u_zs in
                          let occurs_ok, msg = occurs_check env wl (u2,k2) sub2 in
                          if not occurs_ok
                          then giveup_or_defer orig "flex-flex: failed occurs check"
                          else let sol2 = (u2,k2), sub2 in
                               let wl = solve_prob orig None [sol1;sol2] wl in
                               solve env wl in

        let solve_one_pat (t1, u1, k1, xs) (t2, u2, k2, args2) =
            begin
                if Env.debug env <| Options.Other "Rel"
                then Util.fprint2 "Trying flex-flex one pattern (%s) with %s\n" (Print.term_to_string t1) (Print.term_to_string t2);
                if Unionfind.equivalent u1 u2
                then let sub_probs = List.map2
                         (fun (a, _) (t2, _) -> mk_problem (p_scope orig) orig (S.bv_to_name a) EQ t2 None "flex-flex index" |> TProb)
                         xs args2 in
                     let guard = Util.mk_conj_l (List.map (fun p -> p_guard p |> fst) sub_probs) in
                     let wl = solve_prob orig (Some guard) [] wl in
                     solve env (attempt sub_probs wl)
                else
                     let t2 = sn env t2 in
                     let rhs_vars = Free.names t2 in
                     let occurs_ok, _ = occurs_check env wl (u1,k1) t2 in
                     let lhs_vars = Free.names_of_binders xs in
                     if occurs_ok 
                     && Util.set_is_subset_of rhs_vars lhs_vars
                     then let sol = ((u1, k1), U.abs xs t2) in
                          let wl = solve_prob orig None [sol] wl in
                          solve env wl
                     else if occurs_ok && not <| wl.defer_ok
                     then let sol, (_, u2, k2, ys) = force_quasi_pattern (Some xs) (t2, u2, k2, args2) in
                          let wl = extend_solution sol wl in
                          let _ = if Env.debug env <| Options.Other "QuasiPattern" 
                                  then Util.fprint1 "flex-flex quasi pattern (2): %s\n" (uvi_to_string env sol) in
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
            | Some xs, Some ys -> solve_both_pats wl (u1, k1, xs) (u2, k2, ys) (Recheck.check t2) t2.pos
            | Some xs, None -> solve_one_pat (t1, u1, k1, xs) rhs
            | None, Some ys -> solve_one_pat (t2, u2, k2, ys) lhs
            | _ ->
              if wl.defer_ok
              then giveup_or_defer orig "flex-flex: neither side is a pattern"
              else let sol, _ = force_quasi_pattern None (t1, u1, k1, args1) in
                   let wl = extend_solution sol wl in
                   let _ = if Env.debug env <| Options.Other "QuasiPattern" 
                           then Util.fprint1 "flex-flex quasi pattern (1): %s\n" (uvi_to_string env sol) in
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
        then Util.fprint2 "Attempting %s\n\tSubst is %s\n" (prob_to_string env orig) (List.map (uvi_to_string wl.tcenv) wl.subst |> String.concat "; ") in
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
      | Tm_bvar _, _
      | _, Tm_bvar _ -> failwith "Only locally nameless! We should never see a de Bruijn variable"

      | Tm_bvar a, Tm_bvar b ->
        if S.bv_eq a b
        then solve env (solve_prob orig None [] wl)
        else solve env (solve_prob orig (Some <| Util.mk_eq_typ t1 t2) [] wl)

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
            let rel = if !Options.use_eq_at_higher_order then EQ else problem.relation in
            CProb <| mk_problem scope orig c1 rel c2 None "function co-domain")

      | Tm_abs(bs1, t1'), Tm_abs(bs2, t2') ->
        let mk_t t = function
            | [] -> t
            | bs -> mk (Tm_abs(bs, t)) None t.pos in
        let (bs1, t1'), (bs2, t2') =
            match_num_binders (bs1, mk_t t1') (bs2, mk_t t2') in
        solve_binders env bs1 bs2 orig wl
        (fun scope env subst ->
            let t1 = Subst.subst subst t1 in 
            let t2 = Subst.subst subst t2 in //open both bodies
            TProb <| mk_problem scope orig t1 problem.relation t2 None "lambda co-domain")

      | Tm_refine _, Tm_refine _ ->
        let x1, phi1 = as_refinement env wl t1 in
        let x2, phi2 = as_refinement env wl t2 in
        let base_prob = TProb <| mk_problem (p_scope orig) orig x1.sort problem.relation x2.sort problem.element "refinement base type" in
        let x1 = freshen_bv x1 in
        let subst = [DB(0, S.bv_to_name x1)] in
        let phi1 = Subst.subst subst phi1 in
        let phi2 = Subst.subst subst phi2 in
        let env = Env.push_local_binding env (Env.Binding_var(x1, ([], x1.sort))) in
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
      | Tm_uvar _,                Tm_uvar _
      | Tm_app({n=Tm_uvar _}, _), Tm_uvar _
      | Tm_uvar _,                Tm_app({n=Tm_uvar _}, _)
      | Tm_app({n=Tm_uvar _}, _), Tm_app({n=Tm_uvar _}, _) ->
        flex_flex orig (destruct_flex_t t1) (destruct_flex_t t2)
           
      (* flex-rigid equalities *)
      | Tm_uvar _, _
      | Tm_app({n=Tm_uvar _}, _), _ when (problem.relation=EQ) -> (* just imitate/project ... no slack *)
        solve_t_flex_rigid orig (destruct_flex_pattern env t1) t2 wl

      (* rigid-flex: reorient if it is an equality constraint *)
      | _, Tm_uvar _
      | _, Tm_app({n=Tm_uvar _}, _) when (problem.relation = EQ) ->
        solve_t env (invert problem) wl

      (* flex-rigid: subtyping *)
      | Tm_uvar _, _
      | Tm_app({n=Tm_uvar _}, _), _ -> (* equate with the base type of the refinement on the RHS, and add a logical guard for the refinement formula *)
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

      | Tm_name _, _
      | Tm_constant _, _
      | Tm_fvar _, _
      | Tm_app _, _
      | _, Tm_name _
      | _, Tm_constant _
      | _, Tm_fvar _
      | _, Tm_app _ ->
         let m, o = head_matches_delta env wl t1 t2 in
         begin match m, o  with
            | (MisMatch, _) -> //heads definitely do not match
              let head1 = Util.head_and_args t1 |> fst in
              let head2 = Util.head_and_args t2 |> fst in
              let may_equate head = match head.n with
                | Tm_name _  -> true
                | Tm_fvar (tc, _) -> Env.is_projector env tc.v
                | _ -> false  in
              if (may_equate head1 || may_equate head2) && wl.smt_ok
              then solve env (solve_prob orig (Some <| Util.mk_eq_typ t1 t2) [] wl)
              else giveup env "head mismatch" orig

            | (_, Some (t1, t2)) -> //heads match after some delta steps
              solve_t env ({problem with lhs=t1; rhs=t2}) wl

            | (_, None) -> //head matches head'
                if debug env <| Options.Other "Rel" 
                then Util.fprint2 "Head matches: %s and %s\n" (Print.term_to_string t1) (Print.term_to_string t2);
                let head, args = Util.head_and_args t1 in
                let head', args' = Util.head_and_args t2 in
                let nargs = List.length args in
                if nargs <> List.length args'
                then giveup env (Util.format4 "unequal number of arguments: %s[%s] and %s[%s]"
                            (Print.term_to_string head)
                            (args_to_string args)
                            (Print.term_to_string head')
                            (args_to_string args'))
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
                                       then failwith (Util.format2 "Assertion failed: expected full match of %s and %s\n" 
                                                        (Print.term_to_string head) 
                                                        (Print.term_to_string head')) in
                               let subprobs = List.map2 (fun (a, _) (a', _) -> TProb <| mk_problem (p_scope orig) orig a EQ a' None "index") args args' in
                               let formula = Util.mk_conj_l (List.map (fun p -> fst (p_guard p)) subprobs) in
                               let wl = solve_prob orig (Some formula) [] wl in
                               solve env (attempt subprobs wl)

                              | _ ->
                               let lhs = force_refinement (base1, refinement1) in
                               let rhs = force_refinement (base2, refinement2) in
                               solve_t env ({problem with lhs=lhs; rhs=rhs}) wl
                    end
          end

      | Tm_let _, _
      | Tm_ascribed _ , _
      | Tm_meta _, _
      | Tm_delayed _, _
      | _, Tm_ascribed _
      | _, Tm_meta _
      | _, Tm_delayed _
      | _, Tm_let _ -> failwith "Impossible"

      | _ -> giveup env "head mismatch" orig

and solve_c (env:Env.env) (problem:problem<comp,unit>) (wl:worklist) : solution =
    let c1 = problem.lhs in
    let c2 = problem.rhs in
    let orig = CProb problem in
    let sub_prob : 'a -> rel -> 'a -> string -> problem_t<'a,'b> =
        fun t1 rel t2 reason -> mk_problem (p_scope orig) orig t1 rel t2 None reason in
    let solve_eq c1_comp c2_comp =
        let _ = if Env.debug env <| Options.Other "EQ"
                then Util.print_string "solve_c is using an equality constraint\n" in
        let sub_probs = List.map2 (fun (a1, _) (a2, _) -> TProb<| sub_prob a1 EQ a2 "effect arg") 
                        c1_comp.effect_args 
                        c2_comp.effect_args in
        let guard = Util.mk_conj_l (List.map (fun p -> p_guard p |> fst) sub_probs) in
        let wl = solve_prob orig (Some guard) [] wl in
        solve env (attempt sub_probs wl) in
    if Util.physical_equality c1 c2
    then solve env (solve_prob orig None [] wl)
    else let _ = if debug env <| Options.Other "Rel" 
                 then Util.fprint3 "solve_c %s %s %s\n" 
                                    (Print.comp_to_string c1) 
                                    (rel_to_string problem.relation) 
                                    (Print.comp_to_string c2) in
         let r = Env.get_range env in
         let c1_0, c2_0 = c1, c2 in
         match c1.n, c2.n with
               | Total t1, Total t2 -> //rigid-rigid 1
                 solve_t env (problem_using_guard orig t1 problem.relation t2 None "result type") wl

               | Total _,  Comp _ ->
                 solve_c env ({problem with lhs=mk_Comp <| U.comp_to_comp_typ c1}) wl
               | Comp _, Total _ ->
                 solve_c env ({problem with rhs=mk_Comp <| U.comp_to_comp_typ c2}) wl

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
                         if debug env <| Options.Other "Rel" then Util.fprint2 "solve_c for %s and %s\n" (c1.effect_name.str) (c2.effect_name.str);
                         begin match Env.monad_leq env c1.effect_name c2.effect_name with
                           | None -> giveup env (Util.format2 "incompatible monad ordering: %s </: %s" 
                                                    (Print.lid_to_string c1.effect_name) 
                                                    (Print.lid_to_string c2.effect_name)) orig
                           | Some edge ->
                             if problem.relation = EQ
                             then let wp, wlp = match c1.effect_args with
                                                   | [(wp1,_); (wlp1, _)] -> wp1, wlp1
                                                   | _ -> failwith (Util.format1 "Unexpected number of indices on a normalized effect (%s)" (Range.string_of_range (range_of_lid c1.effect_name))) in
                                  let c1 = {
                                    effect_name=c2.effect_name;
                                    result_typ=c1.result_typ;
                                    effect_args=[arg (edge.mlift c1.result_typ wp); arg (edge.mlift c1.result_typ wlp)];
                                    flags=c1.flags
                                  } in
                                  solve_eq c1 c2
                             else let is_null_wp_2 = c2.flags |> Util.for_some (function TOTAL | MLEFFECT | SOMETRIVIAL -> true | _ -> false) in
                                  let wpc1, wpc2 = match c1.effect_args, c2.effect_args with
                                    | (wp1, _)::_, (wp2, _)::_ -> wp1, wp2
                                    | _ -> failwith (Util.format2 "Got effects %s and %s, expected normalized effects" 
                                                                    (Print.lid_to_string c1.effect_name) 
                                                                    (Print.lid_to_string c2.effect_name)) in
                                  if Util.physical_equality wpc1 wpc2
                                  then solve_t env (problem_using_guard orig c1.result_typ problem.relation c2.result_typ None "result type") wl
                                  else let c2_decl = Env.get_effect_decl env c2.effect_name in
                                       let g =
                                       if is_null_wp_2
                                       then let _ = if debug env <| Options.Other "Rel" then Util.print_string "Using trivial wp ... \n" in
                                            mk (Tm_app(c2_decl.trivial, [arg c1.result_typ; arg <| edge.mlift c1.result_typ wpc1])) 
                                               (Some U.ktype0.n) r
                                       else let wp2_imp_wp1 = mk (Tm_app(c2_decl.wp_binop,
                                                                            [arg c2.result_typ;
                                                                             arg wpc2;
                                                                             arg <| S.fvar None Const.imp_lid r;
                                                                             arg <| edge.mlift c1.result_typ wpc1])) None r in
                                                mk (Tm_app(c2_decl.wp_as_type, [arg c2.result_typ; arg wp2_imp_wp1])) (Some U.ktype0.n) r  in
                                       let base_prob = TProb <| sub_prob c1.result_typ problem.relation c2.result_typ "result type" in
                                       let wl = solve_prob orig (Some <| Util.mk_conj (p_guard base_prob |> fst) g) [] wl in
                                       solve env (attempt [base_prob] wl)
                         end

(* -------------------------------------------------------- *)
(* top-level interface                                      *)
(* -------------------------------------------------------- *)
type guard_formula =
  | Trivial
  | NonTrivial of formula

type implicits = list<(uvar * Range.range)>
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
          then Normalize.term_to_string env f
          else "non-trivial" in
  let carry = List.map (fun (_, x) -> prob_to_string env x) g.deferred |> String.concat ",\n" in
  Util.format2 "\n\t{guard_f=%s;\n\t deferred={\n%s};}\n" form carry

(* ------------------------------------------------*)
(* <guard_formula ops> Operations on guard_formula *)
(* ------------------------------------------------*)
let guard_of_guard_formula g = {guard_f=g; deferred=[]; implicits=[]}

let guard_form g = g.guard_f

let is_trivial g = match g with
    | {guard_f=Trivial; deferred=[]} -> true
    | _ -> false

let trivial_guard = {guard_f=Trivial; deferred=[]; implicits=[]}

let abstract_guard x g = match g with
    | None
    | Some ({guard_f=Trivial}) -> g
    | Some g ->
      let f = match g.guard_f with
        | NonTrivial f -> f
        | _ -> failwith "impossible" in
      Some ({g with guard_f=NonTrivial <| U.abs [mk_binder x] f})

let apply_guard g e = match g.guard_f with
  | Trivial -> g
  | NonTrivial f -> {g with guard_f=NonTrivial <| mk (Tm_app(f, [arg e])) (Some U.ktype0.n) f.pos}

let trivial t = match t with
  | Trivial -> ()
  | NonTrivial _ -> failwith "impossible"

let conj_guard_f g1 g2 = match g1, g2 with
  | Trivial, g
  | g, Trivial -> g
  | NonTrivial f1, NonTrivial f2 -> NonTrivial (Util.mk_conj f1 f2)

let check_trivial t = match t.n with
    | Tm_fvar (tc, _) when (lid_equals tc.v Const.true_lid) -> Trivial
    | _ -> NonTrivial t

let imp_guard_f g1 g2 = match g1, g2 with
  | Trivial, g -> g
  | g, Trivial -> Trivial
  | NonTrivial f1, NonTrivial f2 ->
    let imp = Util.mk_imp f1 f2 in check_trivial imp

let binop_guard f g1 g2 = {guard_f=f g1.guard_f g2.guard_f;
                           deferred=g1.deferred@g2.deferred;
                           implicits=g1.implicits@g2.implicits}
let conj_guard g1 g2 = binop_guard conj_guard_f g1 g2
let imp_guard g1 g2 = binop_guard imp_guard_f g1 g2

let close_guard binders g = match g.guard_f with
    | Trivial -> g
    | NonTrivial f -> {g with guard_f=U.close_forall binders f |> NonTrivial}

let mk_guard g ps slack locs = {guard_f=g;
                                deferred=ps;
                                implicits=[]}

(* ------------------------------------------------*)
(* </guard_formula ops>                            *)
(* ------------------------------------------------*)


let new_t_problem env lhs rel rhs elt loc =
 let reason = if debug env <| Options.Other "ExplainRel"
              then Util.format3 "Top-level:\n%s\n\t%s\n%s" 
                        (Normalize.term_to_string env lhs) (rel_to_string rel) 
                        (Normalize.term_to_string env rhs)
              else "TOP" in
 let p = new_problem env lhs rel rhs elt loc reason in
 p

let new_t_prob env t1 rel t2 =
 let x = S.new_bv (Some <| Env.get_range env) t1 in
 let env = Env.push_local_binding env (Env.Binding_var(x, ([],x.sort))) in
 let p = new_t_problem env t1 rel t2 (Some <| S.bv_to_name x) (Env.get_range env) in
 TProb p, x

let simplify_guard env g = match g.guard_f with
    | Trivial -> g
    | NonTrivial f ->
      if Env.debug env Options.High then Util.fprint1 "Simplifying guard %s\n" (Print.term_to_string f);
      let f = Normalize.normalize [Normalize.Beta; Normalize.Simplify] env f in
      let f = match f.n with
        | Tm_fvar (fv, _) when lid_equals fv.v Const.true_lid -> Trivial
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
      if Env.debug env <| Options.Other "ExplainRel"
      then Util.print_string <| explain env d s;
      err (d,s)

let with_guard env prob dopt = match dopt with
    | None -> None
    | Some d ->
      Some <| simplify_guard env ({guard_f=(p_guard prob |> fst |> NonTrivial); deferred=d; implicits=[]})

let try_teq env t1 t2 : option<guard_t> =
 if debug env <| Options.Other "Rel"
 then Util.fprint2 "try_teq of %s and %s\n" (Print.term_to_string t1) (Print.term_to_string t2);
 let prob = TProb<| new_t_problem env t1 EQ t2 None (Env.get_range env) in
 let g = with_guard env prob <| solve_and_commit env (singleton env prob) (fun _ -> None) in
 g

let teq env t1 t2 : guard_t =
 match try_teq env t1 t2 with
    | None -> raise (Error(Errors.basic_type_error env None t2 t1, Env.get_range env))
    | Some g ->
      if debug env <| Options.Other "Rel" 
      then Util.fprint3 "teq of %s and %s succeeded with guard %s\n" 
                        (Print.term_to_string t1) 
                        (Print.term_to_string t2) 
                        (guard_to_string env g);
      g

let try_subtype env t1 t2 =
 if debug env <| Options.Other "Rel"
 then Util.fprint2 "try_subtype of %s and %s\n" (Normalize.term_to_string env t1) (Normalize.term_to_string env t2);
 let prob, x = new_t_prob env t1 SUB t2 in
 let g = with_guard env prob <| solve_and_commit env (singleton env prob) (fun _ -> None) in
 if debug env <| Options.Other "Rel"
    && Util.is_some g
 then Util.fprint3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" 
                    (Normalize.term_to_string env t1) 
                    (Normalize.term_to_string env t2) 
                    (guard_to_string env (Util.must g));
 abstract_guard x g

let subtype_fail env t1 t2 =
    raise (Error(Errors.basic_type_error env None t2 t1, Env.get_range env))

let subtype env t1 t2 : guard_t =
  match try_subtype env t1 t2 with
    | Some f -> f
    | None -> subtype_fail env t1 t2

let sub_comp env c1 c2 =
  if debug env <| Options.Other "Rel"
  then Util.fprint2 "sub_comp of %s and %s\n" (Print.comp_to_string c1) (Print.comp_to_string c2);
  let rel = if env.use_eq then EQ else SUB in
  let prob = CProb <| new_problem env c1 rel c2 None (Env.get_range env) "sub_comp" in
  with_guard env prob <| solve_and_commit env (singleton env prob)  (fun _ -> None)

let solve_deferred_constraints env (g:guard_t) =
   let fail (d,s) =
      let msg = explain env d s in
      raise (Error(msg, p_loc d)) in
   if Env.debug env <| Options.Other "Rel"
   && List.length g.deferred <> 0
   then begin
    Util.fprint1 "Trying to solve carried problems: begin\n%s\nend\n"
   <| (g.deferred 
       |> List.map (fun (msg, x) ->
                        Util.format4 "(At %s) %s\n%s\nguard is %s\n"
                        (Range.string_of_range <| p_loc x) 
                        msg 
                        (prob_to_string env x) 
                        (Normalize.term_to_string env (p_guard x |> fst))) 
       |> String.concat "\n")
   end;
   let gopt = solve_and_commit env (wl_of_guard env g.deferred) fail in
   match gopt with
    | Some _ -> {g with deferred=[]}
    | _ -> failwith "impossible"

let try_discharge_guard env (g:guard_t) =
   let g = solve_deferred_constraints env g in
   if not (Options.should_verify env.curmodule.str) then ()
   else match g.guard_f with
    | Trivial -> ()
    | NonTrivial vc ->
        let vc = Normalize.normalize [N.DeltaHard; N.Beta; N.Eta; N.Simplify] env vc in
        begin match check_trivial vc with
            | Trivial -> ()
            | NonTrivial vc ->
                if Env.debug env <| Options.Other "Rel" 
                then Errors.diag (Env.get_range env) 
                                 (Util.format1 "Checking VC=\n%s\n" (Print.term_to_string vc));
                env.solver.solve env vc
        end
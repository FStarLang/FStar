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
open FStar.ST
open FStar.Exn
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
open FStar.Syntax

module BU = FStar.Util //basic util
module U = FStar.Syntax.Util
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module N = FStar.TypeChecker.Normalize
module UF = FStar.Syntax.Unionfind
module Const = FStar.Parser.Const

let print_ctx_uvar ctx_uvar = Print.ctx_uvar_to_string ctx_uvar


(* Instantiation of unification variables *)
type uvi =
    | TERM of ctx_uvar * term
    | UNIV of S.universe_uvar * universe

(* The set of problems currently being addressed *)
type worklist = {
    attempting:   probs;
    wl_deferred:  list<(int * string * prob)>;  //flex-flex cases, non patterns, and subtyping constraints involving a unification variable,
    ctr:          int;                          //a counter incremented each time we extend subst, used to detect if we've made progress
    defer_ok:     bool;                       //whether or not carrying constraints is ok---at the top-level, this flag is false
    smt_ok:       bool;                       //whether or not falling back to the SMT solver is permitted
    tcenv:        Env.env;
    wl_implicits: implicits;                  //additional uvars introduced
}

(* --------------------------------------------------------- *)
(* <new_uvar> Generating new unification variables/patterns  *)
(* --------------------------------------------------------- *)
let new_uvar reason wl r gamma binders k should_check : ctx_uvar * term * worklist =
    let ctx_uvar = {
         ctx_uvar_head=UF.fresh();
         ctx_uvar_gamma=gamma;
         ctx_uvar_binders=binders;
         ctx_uvar_typ=k;
         ctx_uvar_reason=reason;
         ctx_uvar_should_check=should_check;
         ctx_uvar_range=r
       } in
    check_uvar_ctx_invariant reason r true gamma binders;
    let t = mk (Tm_uvar (ctx_uvar, ([], NoUseRange))) None r in
    let imp = { imp_reason = reason
              ; imp_tm     = t
              ; imp_uvar   = ctx_uvar
              ; imp_range  = r
              ; imp_meta   = None
              } in
    ctx_uvar, t, {wl with wl_implicits=imp::wl.wl_implicits}

let copy_uvar u (bs:binders) t wl =
    let env = {wl.tcenv with gamma = u.ctx_uvar_gamma } in
    let env = Env.push_binders env bs in
    new_uvar u.ctx_uvar_reason wl u.ctx_uvar_range env.gamma
            (Env.all_binders env) t u.ctx_uvar_should_check

(* --------------------------------------------------------- *)
(* </new_uvar>                                               *)
(* --------------------------------------------------------- *)

(* Types used in the output of the solver *)
type solution =
  | Success of deferred * implicits
  | Failed  of prob * string

type variance =
    | COVARIANT
    | CONTRAVARIANT
    | INVARIANT

type tprob = problem<typ>
type cprob = problem<comp>
type problem_t<'a> = problem<'a>

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

let term_to_string t =
    let head, args = U.head_and_args t in
    match head.n with
    | Tm_uvar (u, s) ->
      BU.format3 "%s%s %s"
            (Print.ctx_uvar_to_string u)
            (match fst s with | [] -> "" | s -> BU.format1 "@<%s>" (Print.subst_to_string (List.hd s)))
            (Print.args_to_string args)
    | _ -> Print.term_to_string t


let prob_to_string env = function
  | TProb p ->
    BU.format "\n%s:\t%s \n\t\t%s\n\t%s\n" //\twith guard %s\n\telement= %s\n" //  (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
        [(BU.string_of_int p.pid);
         (term_to_string p.lhs);
         (rel_to_string p.relation);
         (term_to_string p.rhs);
         //(term_to_string p.logical_guard);
         //(match p.element with None -> "none" | Some t -> term_to_string t)
         (* (N.term_to_string env (fst p.logical_guard)); *)
         (* (p.reason |> String.concat "\n\t\t\t") *)]
  | CProb p ->
    BU.format4 "\n%s:\t%s \n\t\t%s\n\t%s"
                 (BU.string_of_int p.pid)
                 (N.comp_to_string env p.lhs)
                 (rel_to_string p.relation)
                 (N.comp_to_string env p.rhs)

let uvi_to_string env = function
    | UNIV (u, t) ->
      let x = if (Options.hide_uvar_nums()) then "?" else UF.univ_uvar_id u |> string_of_int in
      BU.format2 "UNIV %s %s" x (Print.univ_to_string t)

    | TERM (u, t) ->
      let x = if (Options.hide_uvar_nums()) then "?" else UF.uvar_id u.ctx_uvar_head |> string_of_int in
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
    defer_ok=true;
    smt_ok=true;
    wl_implicits=[]
}
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
let make_prob_eq = function
    | TProb p -> TProb ({p with relation=EQ})
    | CProb p -> CProb ({p with relation=EQ})
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
let p_element = function
   | TProb p -> p.element
   | CProb p -> p.element
let p_guard = function
   | TProb p -> p.logical_guard
   | CProb p -> p.logical_guard
let p_guard_uvar = function
   | TProb p -> p.logical_guard_uvar
   | CProb p -> p.logical_guard_uvar
let def_scope_wf msg rng r =
    if not (Options.defensive ()) then () else
    let rec aux prev next =
        match next with
        | [] -> ()
        | (bv, _)::bs ->
          begin
            def_check_closed_in rng msg prev bv.sort;
            aux (prev @ [bv]) bs
          end
    in aux [] r

// Only used for defensive tests now.
let p_scope prob =
   let r = match prob with
   | TProb p -> p.logical_guard_uvar.ctx_uvar_binders @ (match p_element prob with | None -> [] | Some x -> [S.mk_binder x])
   | CProb p -> p.logical_guard_uvar.ctx_uvar_binders @ (match p_element prob with | None -> [] | Some x -> [S.mk_binder x])
   in
   def_scope_wf "p_scope" (p_loc prob) r;
   r

let def_check_scoped msg prob phi =
    if not (Options.defensive ()) then () else
    def_check_closed_in (p_loc prob) msg (List.map fst <| p_scope prob) phi

let def_check_scoped_comp msg prob comp =
    if not (Options.defensive ()) then () else
    (* Cheat *)
    def_check_scoped msg prob (U.arrow [] comp)

let def_check_prob msg prob =
    if not (Options.defensive ()) then () else
    let msgf m = msg ^ "." ^ string_of_int (p_pid prob) ^ "." ^ m in
    def_scope_wf (msgf "scope") (p_loc prob) (p_scope prob);
    def_check_scoped (msgf "guard")      prob (p_guard prob);
    match prob with
    | TProb p ->
        begin
        def_check_scoped (msgf "lhs")        prob p.lhs;
        def_check_scoped (msgf "rhs")        prob p.rhs
        end
    | CProb p ->
        begin
        def_check_scoped_comp (msgf "lhs")        prob p.lhs;
        def_check_scoped_comp (msgf "rhs")        prob p.rhs
        end

let singleton wl prob smt_ok     = {wl with attempting=[prob]; smt_ok = smt_ok}
let wl_of_guard env g            = {empty_worklist env with attempting=List.map snd g}
let defer reason prob wl         = {wl with wl_deferred=(wl.ctr, reason, prob)::wl.wl_deferred}
let attempt probs wl             =
    List.iter (def_check_prob "attempt") probs;
    {wl with attempting=probs@wl.attempting}

let mk_eq2 wl prob t1 t2 : term * worklist =
    (* NS: Rather than introducing a new variable, it would be much preferable
            to simply compute the type of t1 here.
            Sadly, it seems to be way too expensive to call env.type_of here.
    *)
    let t_type, u = U.type_u () in
    let binders = Env.all_binders wl.tcenv in
    let _, tt, wl = new_uvar "eq2" wl t1.pos wl.tcenv.gamma binders t_type Allow_unresolved in
    U.mk_eq2 u tt t1 t2, wl

let p_invert = function
   | TProb p -> TProb <| invert p
   | CProb p -> CProb <| invert p
let is_top_level_prob p = p_reason p |> List.length = 1
let next_pid =
    let ctr = BU.mk_ref 0 in
    fun () -> incr ctr; !ctr

let mk_problem wl scope orig lhs rel rhs elt reason =
    let scope =
        match elt with
        | None -> scope
        | Some x -> scope @ [S.mk_binder x]
    in
    let bs = (p_guard_uvar orig).ctx_uvar_binders @ scope in
    let gamma = List.rev (List.map (fun b -> Binding_var (fst b)) scope) @ (p_guard_uvar orig).ctx_uvar_gamma in
    let ctx_uvar, lg, wl =
        new_uvar ("mk_problem: logical guard for " ^ reason)
                 wl
                 Range.dummyRange
                 gamma
                 bs
                 U.ktype0
                 Allow_untyped
    in
    let prob =
        //logical guards are always squashed;
        //their range is intentionally dummy
        {
             pid=next_pid();
             lhs=lhs;
             relation=rel;
             rhs=rhs;
             element=elt;
             logical_guard=lg;
             logical_guard_uvar=ctx_uvar;
             reason=reason::p_reason orig;
             loc=p_loc orig;
             rank=None;
        }
    in
    (prob, wl)

let mk_t_problem wl scope orig lhs rel rhs elt reason =
  def_check_prob (reason ^ ".mk_t.arg") orig;
  let p, wl = mk_problem wl scope orig lhs rel rhs elt reason in
  def_check_prob (reason ^ ".mk_t") (TProb p);
  TProb p, wl

let mk_c_problem wl scope orig lhs rel rhs elt reason =
  def_check_prob (reason ^ ".mk_c.arg") orig;
  let p, wl = mk_problem wl scope orig lhs rel rhs elt reason in
  def_check_prob (reason ^ ".mk_c") (CProb p);
  CProb p, wl

let new_problem wl env lhs rel rhs (subject:option<bv>) loc reason =
  let lg_ty =
    match subject with
    | None -> U.ktype0
    | Some x ->
      let bs = [S.mk_binder x] in
      U.arrow bs (S.mk_Total U.ktype0)
  in
  let ctx_uvar, lg, wl =
      new_uvar ("new_problem: logical guard for " ^ reason)
               ({wl with tcenv=env})
               loc
               env.gamma
               (Env.all_binders env)
               lg_ty
               Allow_untyped
  in
  let lg =
    match subject with
    | None -> lg
    | Some x -> S.mk_Tm_app lg [S.as_arg <| S.bv_to_name x] None loc
  in
  let prob =
   {
    pid=next_pid();
    lhs=lhs;
    relation=rel;
    rhs=rhs;
    element=subject;
    logical_guard=lg;
    logical_guard_uvar=ctx_uvar;
    reason=[reason];
    loc=loc;
    rank=None;
   } in
   prob, wl

let problem_using_guard orig lhs rel rhs elt reason =
    let p = {
     pid=next_pid();
     lhs=lhs;
     relation=rel;
     rhs=rhs;
     element=elt;
     logical_guard=p_guard orig;
     logical_guard_uvar=p_guard_uvar orig;
     reason=reason::p_reason orig;
     loc=p_loc orig;
     rank=None;
    } in
    def_check_prob reason (TProb p);
    p

let guard_on_element wl problem x phi =
    match problem.element with
        | None ->
          let u = wl.tcenv.universe_of wl.tcenv x.sort in
          U.mk_forall u x phi
        | Some e -> Subst.subst [NT(x,S.bv_to_name e)] phi
let explain env d s =
    if Env.debug env <| Options.Other "ExplainRel"
    ||  Env.debug env <| Options.Other "Rel"
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
        | U_unif u' -> UF.univ_union u u'
        | _ -> UF.univ_change u t
      end
    | TERM(u, t) ->
      def_check_closed_in t.pos "commit" (List.map fst u.ctx_uvar_binders) t;
      U.set_uvar u.ctx_uvar_head t
    )

let find_term_uvar uv s = BU.find_map s (function
    | UNIV _ -> None
    | TERM(u, t) -> if UF.equiv uv u.ctx_uvar_head then Some t else None)

let find_univ_uvar u s = BU.find_map s (function
    | UNIV(u', t) -> if UF.univ_equiv u u' then Some t else None
    | _ -> None)

(* ------------------------------------------------*)
(* </uvi ops>                                      *)
(* ------------------------------------------------*)


(* ------------------------------------------------*)
(* <normalization>                                *)
(* ------------------------------------------------*)
let whnf env t     = SS.compress (N.normalize [Env.Beta; Env.Weak; Env.HNF] env (U.unmeta t)) |> U.unlazy_emb
let sn env t       = SS.compress (N.normalize [Env.Beta] env t) |> U.unlazy_emb
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

let base_and_refinement_maybe_delta should_delta env t1 =
   let norm_refinement env t =
       let steps =
         if should_delta
         then [Env.Weak; Env.HNF; Env.UnfoldUntil delta_constant]
         else [Env.Weak; Env.HNF] in
       N.normalize_refinement steps env t
   in
   let rec aux norm t1 =
        let t1 = U.unmeta t1 in
        match t1.n with
        | Tm_refine(x, phi) ->
            if norm
            then (x.sort, Some(x, phi))
            else (match norm_refinement env t1 with
                 | {n=Tm_refine(x, phi)} -> (x.sort, Some(x, phi))
                 | tt -> failwith (BU.format2 "impossible: Got %s ... %s\n"
                                               (Print.term_to_string tt)
                                               (Print.tag_of_term tt))
                 )

        | Tm_lazy i -> aux norm (U.unfold_lazy i)

        | Tm_uinst _
        | Tm_fvar _
        | Tm_app _ ->
            if norm
            then (t1, None)
            else let t1' = norm_refinement env t1 in
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
        | Tm_quoted _
        | Tm_uvar _
        | Tm_let _
        | Tm_match _ -> (t1, None)

        | Tm_meta _
        | Tm_ascribed _  //NS: Why are the two previous cases excluded? Because of the whnf/unmeta
        | Tm_delayed _
        | Tm_unknown -> failwith (BU.format2 "impossible (outer): Got %s ... %s\n" (Print.term_to_string t1) (Print.tag_of_term t1)) in

   aux false (whnf env t1)

let base_and_refinement env t : term * option<(bv * term)> =
    base_and_refinement_maybe_delta false env t

let normalize_refinement steps env t0 : term =
    N.normalize_refinement steps env t0

let unrefine env t : term =
    base_and_refinement env t |> fst

let trivial_refinement t : bv * term =
    S.null_bv t, U.t_true

let as_refinement delta env t : bv * term =
    let t_base, refinement = base_and_refinement_maybe_delta delta env t in
    match refinement with
        | None -> trivial_refinement t_base
        | Some (x, phi) -> x, phi

let force_refinement (t_base, refopt) : term =
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

let wl_prob_to_string wl prob = prob_to_string wl.tcenv prob
let wl_to_string wl =
    List.map (wl_prob_to_string wl) (wl.attempting@(wl.wl_deferred |> List.map (fun (_, _, x) -> x))) |> String.concat "\n\t"

(* ------------------------------------------------ *)
(* </printing worklists>                             *)
(* ------------------------------------------------ *)

type flex_t = (term * ctx_uvar * args)

let flex_t_to_string (_, c, args) =
    BU.format2 "%s [%s]" (print_ctx_uvar c) (Print.args_to_string args)

let is_flex t =
    let head, _args = U.head_and_args t in
    match (SS.compress head).n with
    | Tm_uvar _ -> true
    | _ -> false

let flex_uvar_head t =
    let head, _args = U.head_and_args t in
    match (SS.compress head).n with
    | Tm_uvar (u, _) -> u
    | _ -> failwith "Not a flex-uvar"

let destruct_flex_t t wl : flex_t * worklist =
    let head, args = U.head_and_args t in
    match (SS.compress head).n with
    | Tm_uvar (uv, ([], _)) -> (t, uv, args), wl
    | Tm_uvar (uv, s) ->
      //let dom_s = s |> List.collect (function NT(x, _) | NM(x, _) -> [S.mk_binder x] | _ -> []) in
      let new_gamma, dom_binders_rev =
          uv.ctx_uvar_gamma |> List.partition (function
          | Binding_var x ->
            let t_x = S.bv_to_name x in
            let t_x' = SS.subst' s t_x in
            (match (SS.compress t_x').n with
             | Tm_name y ->
               S.bv_eq x y //not in the substitution if true
             | _ ->
               false)
          | _ -> true)
      in
      let dom_binders = List.collect (function Binding_var x -> [S.mk_binder x] | _ -> []) dom_binders_rev |> List.rev in
      let v, t_v, wl = new_uvar (uv.ctx_uvar_reason ^ "; force delayed")
                       wl
                       t.pos
                       new_gamma
                       (new_gamma |> List.collect (function Binding_var x -> [S.mk_binder x] | _ -> []) |> List.rev)
                       (U.arrow dom_binders (S.mk_Total uv.ctx_uvar_typ))
                       uv.ctx_uvar_should_check
      in
      let args_sol = List.map (fun (x, i) -> S.bv_to_name x, i) dom_binders in
      let sol = S.mk_Tm_app t_v args_sol None t.pos in
      let args_sol_s = List.map (fun (a, i) -> SS.subst' s a, i) args_sol in
      let all_args = args_sol_s @ args in
      let t = S.mk_Tm_app t_v all_args None t.pos in
      Unionfind.change uv.ctx_uvar_head sol;
      (t, v, all_args), wl

    | _ -> failwith "Not a flex-uvar"

(* ------------------------------------------------ *)
(* <solving problems>                               *)
(* ------------------------------------------------ *)

let u_abs (k : typ) (ys : binders) (t : term) : term =
    let (ys, t), (xs, c) = match (SS.compress k).n with
        | Tm_arrow(bs, c) ->
          if List.length bs = List.length ys
          then (ys, t), SS.open_comp bs c
          else let ys', t, _ = U.abs_formals t in
               (ys@ys', t), U.arrow_formals_comp k
        | _ -> (ys, t), ([], S.mk_Total k) in
    if List.length xs <> List.length ys
    (* TODO : not putting any cflags here on the annotation... *)
    then //The annotation is imprecise, due to a discrepancy in currying/eta-expansions etc.;
         //causing a loss in precision for the SMT encoding
         U.abs ys t (Some (U.mk_residual_comp Const.effect_Tot_lid None []))
    else let c = Subst.subst_comp (U.rename_binders xs ys) c in
         U.abs ys t (Some (U.residual_comp_of_comp c))

let solve_prob' resolve_ok prob logical_guard uvis wl =
    def_check_prob "solve_prob'" prob;
    let phi = match logical_guard with
      | None -> U.t_true
      | Some phi -> phi in
    let assign_solution xs uv phi =
        if Env.debug wl.tcenv <| Options.Other "Rel"
        then BU.print3 "Solving %s (%s) with formula %s\n"
                            (string_of_int (p_pid prob))
                            (print_ctx_uvar uv)
                            (Print.term_to_string phi);
        let phi = U.abs xs phi (Some (U.residual_tot U.ktype0)) in
        def_check_closed_in (p_loc prob) ("solve_prob'.sol." ^ string_of_int (p_pid prob))
                            (List.map fst <| p_scope prob) phi;
        U.set_uvar uv.ctx_uvar_head phi
    in
    let uv = p_guard_uvar prob in
    let fail () =
        failwith (BU.format2 "Impossible: this instance %s has already been assigned a solution\n%s\n"
                              (Print.ctx_uvar_to_string uv)
                              (Print.term_to_string (p_guard prob)))
    in
    let args_as_binders args =
        args |>
        List.collect (fun (a, i) ->
            match (SS.compress a).n with
            | Tm_name x -> [x, i]
            | _ ->
              fail();
              [])
    in
    let wl =
        let g = whnf wl.tcenv (p_guard prob) in
        if not (is_flex g)
        then if resolve_ok
             then wl
             else (fail(); wl)
        else let (_, uv, args), wl  = destruct_flex_t g wl in
             assign_solution (args_as_binders args) uv phi;
             wl
    in
    commit uvis;
    {wl with ctr=wl.ctr + 1}

let extend_solution pid sol wl =
    if Env.debug wl.tcenv <| Options.Other "Rel"
    then BU.print2 "Solving %s: with [%s]\n" (string_of_int pid) (List.map (uvi_to_string wl.tcenv) sol |> String.concat ", ");
    commit sol;
    {wl with ctr=wl.ctr+1}

let solve_prob (prob : prob) (logical_guard : option<term>) (uvis : list<uvi>) (wl:worklist) : worklist =
    def_check_prob "solve_prob.prob" prob;
    BU.iter_opt logical_guard (def_check_scoped "solve_prob.guard" prob);
    let conj_guard t g = match t, g with
        | _, Trivial -> t
        | None, NonTrivial f -> Some f
        | Some t, NonTrivial f -> Some (U.mk_conj t f) in
    if Env.debug wl.tcenv <| Options.Other "Rel"
    then BU.print2 "Solving %s: with %s\n" (string_of_int <| p_pid prob) (List.map (uvi_to_string wl.tcenv) uvis |> String.concat ", ");
    solve_prob' false prob logical_guard uvis wl

(* ------------------------------------------------ *)
(* </solving problems>                              *)
(* ------------------------------------------------ *)


(* ------------------------------------------------ *)
(* <variable ops> common ops on variables           *)
(* ------------------------------------------------ *)
let occurs (uk:ctx_uvar) t =
    let uvars =
        Free.uvars t
        |> BU.set_elements
    in
    let occurs =
        (uvars
        |> BU.for_some (fun uv ->
           UF.equiv uv.ctx_uvar_head uk.ctx_uvar_head))
    in
    uvars, occurs
let occurs_check (uk:ctx_uvar) t =
    let uvars, occurs = occurs uk t in
    let msg =
        if not occurs then None
        else Some (BU.format2 "occurs-check failed (%s occurs in %s)"
                        (Print.uvar_to_string uk.ctx_uvar_head)
                        (Print.term_to_string t)) in
    uvars, not occurs, msg

let rec maximal_prefix (bs:binders) (bs':binders) : binders * (binders * binders) =
  match bs, bs' with
  | (b, i)::bs_tail, (b', i')::bs'_tail ->
    if S.bv_eq b b'
    then let pfx, rest = maximal_prefix bs_tail bs'_tail in
         (b, i)::pfx, rest
    else [], (bs, bs')
  | _ -> [], (bs, bs')

let extend_gamma (g:gamma) (bs:binders) =
    List.fold_left (fun g (x, _) -> Binding_var x::g) g bs

let gamma_until (g:gamma) (bs:binders) =
    match List.last bs with
    | None -> []
    | Some (x, _) ->
      match BU.prefix_until (function Binding_var x' -> S.bv_eq x x' | _  -> false) g with
      | None -> []
      | Some (_, bx, rest) -> bx::rest


let restrict_ctx (tgt:ctx_uvar) (src:ctx_uvar) wl =
    let pfx, _ = maximal_prefix tgt.ctx_uvar_binders src.ctx_uvar_binders in
    let g = gamma_until src.ctx_uvar_gamma pfx in
    let _, src', wl = new_uvar src.ctx_uvar_reason wl src.ctx_uvar_range g pfx src.ctx_uvar_typ src.ctx_uvar_should_check in
    Unionfind.change src.ctx_uvar_head src';
    wl

let restrict_all_uvars (tgt:ctx_uvar) (sources:list<ctx_uvar>) wl  =
    List.fold_right (restrict_ctx tgt) sources wl

let intersect_binders (g:gamma) (v1:binders) (v2:binders) : binders =
    let as_set v =
        v |> List.fold_left (fun out x -> BU.set_add (fst x) out) S.no_names in
    let v1_set = as_set v1 in
    let ctx_binders =
        List.fold_left (fun out b -> match b with Binding_var x -> BU.set_add x out | _ -> out)
                        S.no_names
                        g
    in
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
        ([], ctx_binders) in
    List.rev isect

let binders_eq v1 v2 =
  List.length v1 = List.length v2
  && List.forall2 (fun (a, _) (b, _) -> S.bv_eq a b) v1 v2

let name_exists_in_binders x bs =
    BU.for_some (fun (y, _) -> S.bv_eq x y) bs

let pat_vars env ctx args : option<binders> =
    let rec aux seen args =
      match args with
      | [] -> Some (List.rev seen)
      | (arg, i)::args ->
        let hd = sn env arg in
        match hd.n with
        | Tm_name a ->
          if name_exists_in_binders a seen
          ||  name_exists_in_binders a ctx
          then None
          else aux ((a, i)::seen) args
        | _ -> None
    in
    aux [] args

(* ------------------------------------------------ *)
(* </variable ops>                                  *)
(* ------------------------------------------------ *)

type match_result =
  | MisMatch of option<delta_depth> * option<delta_depth>
  | HeadMatch of bool // true iff the heads MAY match after further unification, false if already the same
  | FullMatch

let string_of_match_result = function
    | MisMatch (d1, d2) ->
        "MisMatch ("
        ^ FStar.Common.string_of_option Print.delta_depth_to_string d1 ^ ") ("
        ^ FStar.Common.string_of_option Print.delta_depth_to_string d2 ^ ")"
    | HeadMatch u -> "HeadMatch " ^ string_of_bool u
    | FullMatch -> "FullMatch"

let head_match = function
    | MisMatch(i, j) -> MisMatch(i, j)
    | HeadMatch true -> HeadMatch true
    | _ -> HeadMatch false

// GM: This is unused, maybe delete
(* let and_match m1 m2 = *)
(*     match m1 with *)
(*     | MisMatch (i, j) -> MisMatch (i, j) *)
(*     | HeadMatch u -> begin match m2 () with *)
(*                      | MisMatch (i,j) -> MisMatch (i, j) *)
(*                      | _ -> HeadMatch *)
(*                      end *)
(*     | FullMatch -> m2 () *)

let fv_delta_depth env fv =
    let d = Env.delta_depth_of_fv env fv in
    match d with
    | Delta_abstract d ->
      if env.curmodule.str = fv.fv_name.v.nsstr && not env.is_iface  //AR: TODO: this is to prevent unfolding of abstract symbols in the extracted interface
                                                                     //    a better way would be create new fvs with appripriate delta_depth at extraction time
      then d //we're in the defining module
      else delta_constant
    | Delta_constant_at_level i when i > 0 ->
      begin match Env.lookup_definition [Unfold delta_constant] env fv.fv_name.v with
            | None -> delta_constant //there's no definition to unfold, e.g., because it's marked irreducible
            | _ -> d
      end
    | d ->
      d

let rec delta_depth_of_term env t =
    let t = U.unmeta t in
    match t.n with
    | Tm_meta _
    | Tm_delayed _  -> failwith "Impossible"
    | Tm_lazy i -> delta_depth_of_term env (U.unfold_lazy i)
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
    | Tm_quoted _
    | Tm_abs _ -> Some delta_constant
    | Tm_fvar fv -> Some (fv_delta_depth env fv)


let rec head_matches env t1 t2 : match_result =
  let t1 = U.unmeta t1 in
  let t2 = U.unmeta t2 in
  match t1.n, t2.n with
    | Tm_lazy ({lkind=Lazy_embedding _}), _ -> head_matches env (U.unlazy t1) t2
    |  _, Tm_lazy({lkind=Lazy_embedding _}) -> head_matches env t1 (U.unlazy t2)
    | Tm_name x, Tm_name y -> if S.bv_eq x y then FullMatch else MisMatch(None, None)
    | Tm_fvar f, Tm_fvar g -> if S.fv_eq f g then FullMatch else MisMatch(Some (fv_delta_depth env f), Some (fv_delta_depth env g))
    | Tm_uinst (f, _), Tm_uinst(g, _) -> head_matches env f g |> head_match
    | Tm_constant c, Tm_constant d -> if FStar.Const.eq_const c d then FullMatch else MisMatch(None, None)
    | Tm_uvar (uv, _), Tm_uvar (uv', _) -> if UF.equiv uv.ctx_uvar_head uv'.ctx_uvar_head then FullMatch else MisMatch(None, None)

    | Tm_refine(x, _), Tm_refine(y, _) -> head_matches env x.sort y.sort |> head_match

    | Tm_refine(x, _), _  -> head_matches env x.sort t2 |> head_match
    | _, Tm_refine(x, _)  -> head_matches env t1 x.sort |> head_match

    | Tm_type _, Tm_type _
    | Tm_arrow _, Tm_arrow _ -> HeadMatch false

    | Tm_app(head, _), Tm_app(head', _) -> head_matches env head head' |> head_match
    | Tm_app(head, _), _ -> head_matches env head t2 |> head_match
    | _, Tm_app(head, _) -> head_matches env t1 head |> head_match

    | Tm_let _, Tm_let _
    | Tm_match _, Tm_match _ -> HeadMatch true

    | _ -> MisMatch(delta_depth_of_term env t1, delta_depth_of_term env t2)

(* Does t1 head-match t2, after some delta steps? *)
let head_matches_delta env t1 t2 : (match_result * option<(typ*typ)>) =
    let maybe_inline t =
        let head = U.head_of t in
        if Env.debug env <| Options.Other "RelDelta" then
            BU.print2 "Head of %s is %s\n" (Print.term_to_string t) (Print.term_to_string head);
        match (U.un_uinst head).n with
        | Tm_fvar fv ->
          begin match Env.lookup_definition [Env.Unfold delta_constant; Env.Eager_unfolding_only] env fv.fv_name.v with
          | None ->
            if Env.debug env <| Options.Other "RelDelta" then
                BU.print1 "No definition found for %s\n" (Print.term_to_string head);
            None
          | Some _ ->
            let t' = N.normalize [Env.UnfoldUntil delta_constant; Env.Weak; Env.HNF; Env.Primops; Env.Beta; Env.Eager_unfolding; Env.Iota] env t in
            if Env.debug env <| Options.Other "RelDelta" then
                BU.print2 "Inlined %s to %s\n" (Print.term_to_string t) (Print.term_to_string t');
            Some t'
          end
        | _ -> None
    in
    let success d r t1 t2 = (r, (if d>0 then Some(t1, t2) else None)) in
    let fail d r t1 t2 = (r, (if d>0 then Some(t1, t2) else None)) in
    let rec aux retry n_delta t1 t2 =
        let r = head_matches env t1 t2 in
        if Env.debug env <| Options.Other "RelDelta" then
            BU.print3 "head_matches (%s, %s) = %s\n"
                (Print.term_to_string t1)
                (Print.term_to_string t2)
                (string_of_match_result r);
        let reduce_one_and_try_again (d1:delta_depth) (d2:delta_depth) =
          let d1_greater_than_d2 = Common.delta_depth_greater_than d1 d2 in
          let t1, t2 = if d1_greater_than_d2
                       then let t1' = normalize_refinement [Env.UnfoldUntil d2; Env.Weak; Env.HNF] env t1 in
                            t1', t2
                       else let t2' = normalize_refinement [Env.UnfoldUntil d1; Env.Weak; Env.HNF] env t2 in
                            t1, t2' in
          aux retry (n_delta + 1) t1 t2
        in

        let reduce_both_and_try_again (d:delta_depth) (r:match_result) =
          match Common.decr_delta_depth d with
          | None -> fail n_delta r t1 t2
          | Some d ->
            let t1 = normalize_refinement [Env.UnfoldUntil d; Env.Weak; Env.HNF] env t1 in
            let t2 = normalize_refinement [Env.UnfoldUntil d; Env.Weak; Env.HNF] env t2 in
            aux retry (n_delta + 1) t1 t2
        in

        match r with
            | MisMatch (Some (Delta_equational_at_level i), Some (Delta_equational_at_level j)) when (i > 0 || j > 0) && i <> j ->
              reduce_one_and_try_again (Delta_equational_at_level i) (Delta_equational_at_level j)

            | MisMatch(Some (Delta_equational_at_level _), _)
            | MisMatch(_, Some (Delta_equational_at_level _)) ->
              if not retry then fail n_delta r t1 t2
              else begin match maybe_inline t1, maybe_inline t2 with
                   | None, None       -> fail n_delta r t1 t2
                   | Some t1, None    -> aux false (n_delta + 1) t1 t2
                   | None, Some t2    -> aux false (n_delta + 1) t1 t2
                   | Some t1, Some t2 -> aux false (n_delta + 1) t1 t2
                   end

            | MisMatch(Some d1, Some d2) when (d1=d2) -> //incompatible
              reduce_both_and_try_again d1 r

            | MisMatch(Some d1, Some d2) -> //these may be related after some delta steps
              reduce_one_and_try_again d1 d2

            | MisMatch _ ->
              fail n_delta r t1 t2

            | _ ->
              success n_delta r t1 t2 in
    let r = aux true 0 t1 t2 in
    if Env.debug env <| Options.Other "RelDelta" then
        BU.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
            (Print.term_to_string t1)
            (Print.term_to_string t2)
            (string_of_match_result (fst r))
            (if Option.isNone (snd r)
             then "None"
             else snd r
                 |> must
                 |> (fun (t1, t2) ->
                     Print.term_to_string t1
                     ^ "; "
                     ^ Print.term_to_string t2));
    r

let kind_type (binders:binders) (r:Range.range) =
    U.type_u() |> fst


(* ----------------------------------------------------- *)
(* Ranking problems for the order in which to solve them *)
(* ----------------------------------------------------- *)
let rank_t_num = function
    | Rigid_rigid -> 0
    | Flex_rigid_eq -> 1
    | Flex_flex_pattern_eq -> 2
    | Flex_rigid -> 3
    | Rigid_flex -> 4
    | Flex_flex -> 5
let rank_leq r1 r2 = rank_t_num r1 <= rank_t_num r2
let rank_less_than r1 r2 =
    //writing it as `rank_t_num r1 < rank_t_num r2`
    //doesn't parse in the F# build of F* with #light "off" (!)
    r1 <> r2 &&
    rank_t_num r1 <= rank_t_num r2
let compress_tprob tcenv p = {p with lhs=whnf tcenv p.lhs; rhs=whnf tcenv p.rhs}

let compress_prob tcenv p =
    match p with
    | TProb p -> compress_tprob tcenv p |> TProb
    | CProb _ -> p


let rank tcenv pr : rank_t    //the rank
                  * prob   //the input problem, pre-processed a bit (the wl is needed for the pre-processing)
                  =
   let prob = compress_prob tcenv pr |> maybe_invert_p in
   match prob with
    | TProb tp ->
      let lh, lhs_args = U.head_and_args tp.lhs in
      let rh, rhs_args = U.head_and_args tp.rhs in
      let rank, tp =
        match lh.n, rh.n with
        | Tm_uvar _, Tm_uvar _ ->
          begin
          match lhs_args, rhs_args with
          | [], [] when tp.relation=EQ ->
            Flex_flex_pattern_eq, tp
          | _ -> Flex_flex, tp
          end

        | Tm_uvar _, _
        | _, Tm_uvar _ when tp.relation=EQ ->
          Flex_rigid_eq, tp

        | Tm_uvar _, Tm_arrow _
        | Tm_uvar _, Tm_type _
        | Tm_type _, Tm_uvar _ ->
          //this case is so common, that even though we could delay, it is almost always ok to solve it immediately as an equality
          //besides, in the case of arrows, if we delay it, the arity of various terms built by the unifier goes awry
          //so, don't delay!
          Flex_rigid_eq, {tp with relation=EQ}

        | _, Tm_uvar _ ->
          Rigid_flex, tp

        | Tm_uvar _, _ ->
          Flex_rigid, tp

        | _, Tm_uvar _ ->
          Rigid_flex, tp

        | _, _ ->
          Rigid_rigid, tp
      in
      rank, {tp with rank=Some rank} |> TProb

    | CProb cp ->
      Rigid_rigid, {cp with rank=Some Rigid_rigid} |> CProb

let next_prob wl : option<(prob * list<prob> * rank_t)> =
                  //a problem with the lowest rank, or a problem whose rank <= flex_rigid_eq, if any
                  //all the other problems in wl
                  //the rank of the first problem, or the minimum rank in the wl
    let rec aux (min_rank, min, out) probs =
        match probs with
        | [] ->
          begin
          match min, min_rank with
          | Some p, Some r -> Some (p, out, r)
          | _ -> None
          end
        | hd::tl ->
          let rank, hd = rank wl.tcenv hd in
          if rank_leq rank Flex_rigid_eq
          then match min with
               | None -> Some (hd, out@tl, rank)
               | Some m -> Some (hd, out@m::tl, rank)
          else if min_rank = None
               || rank_less_than rank (Option.get min_rank)
          then match min with
               | None -> aux (Some rank, Some hd, out) tl
               | Some m -> aux (Some rank, Some hd, m::out) tl
          else aux (min_rank, min, hd::out) tl
    in
    aux (None, None, []) wl.attempting

let flex_prob_closing tcenv (bs:binders) (p:prob) =
    let flex_will_be_closed t =
        let hd, _ = U.head_and_args t in
        match (SS.compress hd).n with
        | Tm_uvar(u, _) ->
          u.ctx_uvar_binders |> BU.for_some (fun (y, _) ->
          bs |> BU.for_some (fun (x, _) -> S.bv_eq x y))
        | _ -> false
    in
    let r, p = rank tcenv p in
    match p with
    | CProb _ ->
      true
    | TProb p ->
      match r with
      | Rigid_rigid
      | Flex_rigid_eq
      | Flex_flex_pattern_eq ->
        true
      | Flex_rigid ->
        flex_will_be_closed p.lhs
      | Rigid_flex ->
        flex_will_be_closed p.rhs
      | Flex_flex ->
        p.relation=EQ
        &&
        (flex_will_be_closed p.lhs
        || flex_will_be_closed p.rhs)

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
                | U_unif v2 -> UF.univ_equiv v1 v2
                | _ -> false)
        | _ -> occurs_univ v1 (U_max [u]) in

    let rec filter_out_common_univs (u1:list<universe>) (u2:list<universe>) :(list<universe> * list<universe>) =
      let common_elts = u1 |> List.fold_left (fun uvs uv1 -> if u2 |> List.existsML (fun uv2 -> U.compare_univs uv1 uv2 = 0) then uv1::uvs else uvs) [] in
      let filter = List.filter (fun u -> not (common_elts |> List.existsML (fun u' -> U.compare_univs u u' = 0))) in
      filter u1, filter u2
    in

    let try_umax_components u1 u2 msg =
        match u1, u2 with
            | U_max us1, U_max us2 ->
              //filter out common universes in us1 and us2
              //this allows more cases to unify, e.g. us1 = [uvar; un] and us2=[un; un']
              //with just structural comparison, this would fail to unify, but after filtering away un, we can unify uvar with un'
              let us1, us2 = filter_out_common_univs us1 us2 in
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
          if UF.univ_equiv v1 v2
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

(* This balances two lists.  Given (xs, f) (ys, g), it will
 * take a maximal same-length prefix from each list, getting
 *   (xs1, xs2) and (ys1, ys2)  /  where length xs1 == length xs2 (and ys1 = [] \/ ys2 = [])
 * and then return
 *   (xs1, f xs2), (ys1, g ys2)
 *
 * We could find the minimum of their lengths, split, and apply, but this is faster.
 *)
let match_num_binders (bc1: (list<'a> * (list<'a> -> 'b)))
                      (bc2: (list<'a> * (list<'a> -> 'b)))
    : (list<'a> * 'b) * (list<'a> * 'b) =
    let (bs1, mk_cod1) = bc1 in
    let (bs2, mk_cod2) = bc2 in
    let rec aux (bs1 : list<'a>) (bs2 : list<'a>) : (list<'a> * 'b) * (list<'a> * 'b) =
        match bs1, bs2 with
        | x::xs, y::ys ->
            let ((xs, xr), (ys, yr)) = aux xs ys in
            ((x::xs, xr), (y::ys, yr))
        | xs, ys -> // at least one empty
            (([], mk_cod1 xs), ([], mk_cod2 ys))
    in
    aux bs1 bs2

let guard_of_prob (env:Env.env) (wl:worklist) (problem:tprob) (t1 : term) (t2 : term) : term * worklist =
    let has_type_guard t1 t2 =
        match problem.element with
        | Some t ->
            U.mk_has_type t1 (S.bv_to_name t) t2
        | None ->
            let x = S.new_bv None t1 in
            let u_x = env.universe_of env t1 in
            U.mk_forall u_x x (U.mk_has_type t1 (S.bv_to_name x) t2)
    in
    match problem.relation with
    | EQ     -> mk_eq2 wl (TProb problem) t1 t2
    | SUB    -> has_type_guard t1 t2, wl
    | SUBINV -> has_type_guard t2 t1, wl

let is_flex_pat = function
    | _, _, [] -> true
    | _ -> false

(* <quasi_pattern>:
        Given a term (?u_(bs;t) e1..en)
        returns None in case the arity of the type t is less than n
        otherwise returns Some (x1 ... xn)
        where if ei is a variable distinct from bs and all the ej
            then xi = ei
            else xi is a fresh variable
    *)
let quasi_pattern env (f:flex_t) : option<(binders * typ)> =
    let _, {ctx_uvar_binders=ctx; ctx_uvar_typ=t_hd}, args = f in
    let name_exists_in x bs =
        BU.for_some (fun (y, _) -> S.bv_eq x y) bs
    in
    let rec aux pat_binders formals t_res args =
        match formals, args with
        | [], []
        |  _, [] ->
          Some (List.rev pat_binders, U.arrow formals (S.mk_Total t_res))

        | (formal, formal_imp)::formals, (a, a_imp)::args ->
            begin
            match (SS.compress a).n with
            | Tm_name x ->
                if name_exists_in x ctx
                ||  name_exists_in x pat_binders
                then //we already have x
                     //so don't include it in the quasi-pattern
                     aux ((formal, formal_imp) :: pat_binders) formals t_res args
                else let x = {x with sort=formal.sort} in
                        let subst = [NT(formal, S.bv_to_name x)] in
                        let formals = SS.subst_binders subst formals in
                        let t_res = SS.subst subst t_res in
                        aux (({x with sort=formal.sort}, a_imp) :: pat_binders) formals t_res args
            | _ -> //it's not a name, so it can't be included in the patterns
            aux ((formal, formal_imp) :: pat_binders) formals t_res args
            end

        | [], args ->
            let more_formals, t_res = U.arrow_formals (N.unfold_whnf env t_res) in
            begin
            match more_formals with
            | [] -> None //seems ill-typed at this point
            | _ -> aux pat_binders more_formals t_res args
            end
    in
    match args with
    | [] -> Some ([], t_hd) //this really a pattern, not a quasi_pattern
    | _ ->
      let formals, t_res = U.arrow_formals t_hd in
      aux [] formals t_res args

(******************************************************************************************************)
(* Main solving algorithm begins here *)
(******************************************************************************************************)
let rec solve (env:Env.env) (probs:worklist) : solution =
//    printfn "Solving TODO:\n%s;;" (List.map prob_to_string probs.attempting |> String.concat "\n\t");
    if Env.debug env <| Options.Other "Rel"
    then BU.print1 "solve:\n\t%s\n" (wl_to_string probs);
    match next_prob probs with
    | Some (hd, tl, rank) ->
      let probs = {probs with attempting=tl} in
      def_check_prob "solve,hd" hd;
      begin match hd with
      | CProb cp ->
            solve_c env (maybe_invert cp) probs

      | TProb tp ->
        if BU.physical_equality tp.lhs tp.rhs then solve env (solve_prob hd None [] probs) else
        if rank=Rigid_rigid
        || (tp.relation = EQ && rank <> Flex_flex)
        then solve_t' env tp probs
        else if probs.defer_ok
        then solve env (defer "deferring flex_rigid or flex_flex subtyping" hd probs)
        else if rank=Flex_flex
        then solve_t' env ({tp with relation=EQ}) probs //turn flex_flex subtyping into flex_flex eq
        else solve_rigid_flex_or_flex_rigid_subtyping rank env tp probs
      end

    | None ->
         begin
         match probs.wl_deferred with
         | [] ->
           Success ([], probs.wl_implicits) //Yay ... done!

         | _ ->
           let attempt, rest = probs.wl_deferred |> List.partition (fun (c, _, _) -> c < probs.ctr) in
           match attempt with
            | [] -> //can't solve yet; defer the rest
              Success(List.map (fun (_, x, y) -> (x, y)) probs.wl_deferred, probs.wl_implicits)

            | _ ->
              solve env ({probs with attempting=attempt |> List.map (fun (_, _, y) -> y); wl_deferred=rest})
         end

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
(* The case where u < t1, .... u < tn: we solve this by taking u=t1/\.../\tn                          *)
(******************************************************************************************************)
and solve_rigid_flex_or_flex_rigid_subtyping
    (rank:rank_t)
    (env:Env.env) (tp:tprob) (wl:worklist) : solution =
    def_check_prob "solve_rigid_flex_or_flex_rigid_subtyping" (TProb tp);
    let flip = rank = Flex_rigid in
    (*
        meet_or_join op [t1;..;tn] env wl:
            Informally, this computes `t1 op t2 ... op tn`
            where op is either \/ or /\

            t1 op t2 is only defined when t1 and t2
            are refinements of the same base type
    *)
    let meet_or_join op ts env wl =
        let eq_prob t1 t2 wl =
            let p, wl =
            new_problem wl env t1 EQ t2 None t1.pos
                        "join/meet refinements"
            in
            def_check_prob "meet_or_join" (TProb p);
            TProb p, wl
        in
        let pairwise t1 t2 wl =
            if Env.debug env <| Options.Other "Rel"
            then BU.print2 "[meet/join]: pairwise: %s and %s\n" (Print.term_to_string t1) (Print.term_to_string t2);
            let mr, ts = head_matches_delta env t1 t2 in
            match mr with
            | HeadMatch true
            | MisMatch _ ->
              let p, wl = eq_prob t1 t2 wl in
              (t1, [p], wl)

            | FullMatch ->
              begin
              match ts with
              | None ->
                (t1, [], wl)
              | Some (t1, t2) ->
                (t1, [], wl)
              end

            | HeadMatch false ->
              let t1, t2 =
                  match ts with
                  | Some (t1, t2) -> SS.compress t1, SS.compress t2
                  | None -> SS.compress t1, SS.compress t2
              in
              let try_eq t1 t2 wl =
                  let t1_hd, t1_args = U.head_and_args t1 in
                  let t2_hd, t2_args = U.head_and_args t2 in
                  if List.length t1_args <> List.length t2_args then None else
                  let probs, wl =
                          List.fold_left2 (fun (probs, wl) (a1, _) (a2, _) ->
                             let p, wl = eq_prob a1 a2 wl in
                             p::probs, wl)
                          ([], wl)
                   //don't forget to prove t1_hd = t2_hd
                   //as they may have universe variables to equate
                   //as well
                          (as_arg t1_hd::t1_args)
                          (as_arg t2_hd::t2_args)
                  in
                  let wl' = {wl with defer_ok=false;
                                     smt_ok=false;
                                     attempting=probs;
                                     wl_deferred=[];
                                     wl_implicits=[]} in
                  let tx = UF.new_transaction () in
                  match solve env wl' with
                  | Success (_, imps) ->
                    UF.commit tx;
                    Some ({wl with wl_implicits=wl.wl_implicits@imps})

                  | Failed _ ->
                    UF.rollback tx;
                    None
              in
              let combine t1 t2 wl =
                  let t1_base, p1_opt = base_and_refinement_maybe_delta false env t1 in
                  let t2_base, p2_opt = base_and_refinement_maybe_delta false env t2 in
                  let combine_refinements t_base p1_opt p2_opt =
                      let refine x t =
                          if U.is_t_true t then x.sort
                          else U.refine x t
                      in
                      match p1_opt, p2_opt with
                      | Some (x, phi1), Some(y, phi2) ->
                        let x = freshen_bv x in
                        let subst = [DB(0, x)] in
                        let phi1 = SS.subst subst phi1 in
                        let phi2 = SS.subst subst phi2 in
                        refine x (op phi1 phi2)

                      | None, Some (x, phi)
                      | Some(x, phi), None ->
                        let x = freshen_bv x in
                        let subst = [DB(0, x)] in
                        let phi = SS.subst subst phi in
                        refine x (op U.t_true phi)

                      | _ ->
                        t_base
                  in
                  match try_eq t1_base t2_base wl with
                  | Some wl ->
                    combine_refinements t1_base p1_opt p2_opt,
                    [],
                    wl

                  | None ->
                    let t1_base, p1_opt = base_and_refinement_maybe_delta true env t1 in
                    let t2_base, p2_opt = base_and_refinement_maybe_delta true env t2 in
                    let p, wl = eq_prob t1_base t2_base wl in
                    let t = combine_refinements t1_base p1_opt p2_opt in
                    (t, [p], wl)
              in
              let t1, ps, wl = combine t1 t2 wl in
              if Env.debug env <| Options.Other "Rel"
              then BU.print1 "pairwise fallback2 succeeded: %s"
                            (Print.term_to_string t1);
              t1, ps, wl
        in
        let rec aux (out, probs, wl) ts =
            match ts with
            | [] -> (out, probs, wl)
            | t::ts ->
              let out, probs', wl = pairwise out t wl in
              aux (out, probs@probs', wl) ts
        in
        aux (List.hd ts, [], wl) (List.tl ts)
    in
    (*end meet_or_join *)

    let this_flex, this_rigid = if flip then tp.lhs, tp.rhs else tp.rhs, tp.lhs in
    begin
    match (SS.compress this_rigid).n with
    | Tm_arrow (_bs, comp) ->
        //Although it's possible to take the meet/join of arrow types
        //we handle them separately either by imitation (for Tot/GTot arrows)
        //which provides some structural subtyping for them
        //or just by reducing it to equality in other cases

        //BEWARE: special treatment of Tot and GTot here
        if U.is_tot_or_gtot_comp comp
        then let flex, wl = destruct_flex_t this_flex wl in
             begin
             match quasi_pattern env flex with
             | None -> giveup env "flex-arrow subtyping, not a quasi pattern" (TProb tp)
             | Some (flex_bs, flex_t) ->
               if Env.debug env <| Options.Other "Rel"
               then BU.print1 "Trying to solve by imitating arrow:%s\n" (string_of_int tp.pid);
               imitate_arrow (TProb tp) env wl flex flex_bs flex_t tp.relation this_rigid
             end
        else //imitating subtyping with WPs is hopeless
             solve env (attempt [TProb ({tp with relation=EQ})] wl)

  | _ ->
    if Env.debug env <| Options.Other "Rel"
    then BU.print1 "Trying to solve by meeting refinements:%s\n" (string_of_int tp.pid);
    let u, _args = U.head_and_args this_flex in
    begin
    match (SS.compress u).n with
    | Tm_uvar(ctx_uvar, _subst) ->
      let equiv t =
         let u', _ = U.head_and_args t in
         match (whnf env u').n with
         | Tm_uvar(ctx_uvar', _subst') ->
           UF.equiv ctx_uvar.ctx_uvar_head ctx_uvar'.ctx_uvar_head
         | _ -> false
      in
     //find all other constraints of the form t <: u, or if flipped, u <: t
      let bounds_probs, rest =
          wl.attempting |> List.partition
         (function
          | TProb tp ->
            let tp = maybe_invert tp in
            begin
            match tp.rank with
            | Some rank' when rank=rank' ->
              if flip then equiv tp.lhs else equiv tp.rhs

            | _ -> false
            end

           | _ -> false)
      in
      let bounds_typs =
          whnf env this_rigid
          :: List.collect (function
                           | TProb p -> [(if flip
                                         then whnf env (maybe_invert p).rhs
                                         else whnf env (maybe_invert p).lhs)]
                           | _ -> [])
                          bounds_probs
      in
      let (bound, sub_probs, wl) =
         meet_or_join (if flip then U.mk_conj_simp else U.mk_disj_simp)
                      bounds_typs
                      env
                      wl
      in
      let bound_typ, (eq_prob, wl') =
          let flex_u = flex_uvar_head this_flex in
          let bound =
            //We get constraints of the form (x:?u{phi} <: ?u)
            //This cannot be solved with an equality constraints
            //So, turn the bound on the LHS to just ?u
            match (SS.compress bound).n with
            | Tm_refine (x, phi)
              when tp.relation=SUB
                && snd (occurs flex_u x.sort) ->
              x.sort
            | _ ->
              bound
          in
          bound,
          new_problem wl env bound EQ this_flex None tp.loc
                (if flip then "joining refinements" else "meeting refinements")
      in
      def_check_prob "meet_or_join2" (TProb eq_prob);
      let _ = if Env.debug env <| Options.Other "Rel"
              then let wl' = {wl with attempting=TProb eq_prob::sub_probs} in
                   BU.print1 "After meet/join refinements: %s\n" (wl_to_string wl') in

      let tx = UF.new_transaction () in
      begin
      match solve_t env eq_prob ({wl' with defer_ok=false; attempting=sub_probs}) with
      | Success _ ->
         let wl = {wl' with attempting=rest} in
         let g =  List.fold_left (fun g p -> U.mk_conj g (p_guard p))
                                 eq_prob.logical_guard
                                 sub_probs in
         let wl = solve_prob' false (TProb tp) (Some g) [] wl in
         let _ = List.fold_left (fun wl p -> solve_prob' true p None [] wl) wl bounds_probs in
         UF.commit tx;
         solve env wl

      | Failed (p, msg) ->
         if Env.debug env <| Options.Other "Rel"
         then BU.print1 "meet/join attempted and failed to solve problems:\n%s\n"
                        (List.map (prob_to_string env) (TProb eq_prob::sub_probs) |> String.concat "\n");
         (match rank, base_and_refinement env bound_typ with
          | Rigid_flex, (t_base, Some _) ->
            UF.rollback tx;
              //We failed to solve (x:t_base{p} <: ?u) while computing a precise join of all the lower bounds
              //Rather than giving up, try again with a widening heuristic
              //i.e., try to solve ?u = t and proceed
            let eq_prob, wl =
                new_problem wl env t_base EQ this_flex None tp.loc "widened subtyping" in
            def_check_prob "meet_or_join3" (TProb eq_prob);
            let wl = solve_prob' false (TProb tp) (Some (p_guard (TProb eq_prob))) [] wl in
            solve env (attempt [TProb eq_prob] wl)

          | Flex_rigid, (t_base, Some (x, phi)) ->
            UF.rollback tx;
              //We failed to solve (?u = x:t_base{phi}) while computing
              //a precise meet of all the upper bounds
              //Rather than giving up, try again with a narrowing heuristic
              //i.e., solve ?u = t_base, with the guard formula phi
            let eq_prob, wl =
                new_problem wl env t_base EQ this_flex None tp.loc "widened subtyping" in
            def_check_prob "meet_or_join4" (TProb eq_prob);
            let phi = guard_on_element wl tp x phi in
            let wl = solve_prob' false (TProb tp) (Some (U.mk_conj phi (p_guard (TProb eq_prob)))) [] wl in
            solve env (attempt [TProb eq_prob] wl)

          | _ ->
            giveup env ("failed to solve sub-problems: " ^msg) p)
      end

    | _ when flip ->
      failwith (BU.format2 "Impossible: (rank=%s) Not a flex-rigid: %s"
                            (BU.string_of_int (rank_t_num rank))
                            (prob_to_string env (TProb tp)))
    | _ ->
      failwith (BU.format2 "Impossible: (rank=%s) Not a rigid-flex: %s"
                            (BU.string_of_int (rank_t_num rank))
                            (prob_to_string env (TProb tp)))
    end
  end

and imitate_arrow (orig:prob) (env:Env.env) (wl:worklist)
                  (lhs:flex_t) (bs_lhs:binders) (t_res_lhs:term)
                  (rel:rel)
                  (arrow:term)
        : solution =
        let bs_lhs_args = List.map (fun (x, i) -> S.bv_to_name x, i) bs_lhs in
        let _, u_lhs, _ = lhs in
        let imitate_comp bs bs_terms c wl =
           let imitate_tot_or_gtot t uopt f wl =
              let k, univ =
                  match uopt with
                  | None ->
                    U.type_u()
                  | Some univ ->
                    S.mk (Tm_type univ) None t.pos, univ
              in
              let _, u, wl = copy_uvar u_lhs (bs_lhs@bs) k wl in
              f u (Some univ), wl
           in
           match c.n with
           | Total (t, uopt) ->
             imitate_tot_or_gtot t uopt S.mk_Total' wl
           | GTotal (t, uopt) ->
             imitate_tot_or_gtot t uopt S.mk_GTotal' wl
           | Comp ct ->
             let out_args, wl =
               List.fold_right
                 (fun (a, i) (out_args, wl) ->
                   let _, t_a, wl = copy_uvar u_lhs [] (fst <| U.type_u()) wl in
                   let _, a', wl = copy_uvar u_lhs bs t_a wl in
                   (a',i)::out_args, wl)
                 ((S.as_arg ct.result_typ)::ct.effect_args)
                 ([], wl)
             in
             let ct' = {ct with result_typ=fst (List.hd out_args);
                                effect_args=List.tl out_args} in
             {c with n=Comp ct'}, wl
        in
        let formals, c = U.arrow_formals_comp arrow in
        let rec aux (bs:binders) (bs_terms:list<arg>) (formals:binders) wl =
            match formals with
            | [] ->
              let c', wl = imitate_comp bs bs_terms c wl in
              let lhs' = U.arrow bs c' in
              let sol = TERM (u_lhs, U.abs bs_lhs lhs' (Some (U.residual_tot t_res_lhs))) in
              let sub_prob, wl =
                  mk_t_problem wl [] orig lhs' rel arrow None "arrow imitation"
              in
              //printfn "Arrow imitation: %s =?= %s" (Print.term_to_string lhs') (Print.term_to_string rhs);
              solve env (attempt [sub_prob] (solve_prob orig None [sol] wl))

            | (x, imp)::formals ->
              let _ctx_u_x, u_x, wl = copy_uvar u_lhs (bs_lhs@bs) (U.type_u() |> fst) wl in
              //printfn "Generated formal %s where %s" (Print.term_to_string t_y) (Print.ctx_uvar_to_string ctx_u_x);
              let y = S.new_bv (Some (S.range_of_bv x)) u_x in
              aux (bs@[y, imp]) (bs_terms@[S.bv_to_name y, imp]) formals wl
         in
         let _, occurs_ok, msg = occurs_check u_lhs arrow in
         if not occurs_ok
         then giveup_or_defer env orig wl ("occurs-check failed: " ^ (Option.get msg))
         else aux [] [] formals wl

and solve_binders (env:Env.env) (bs1:binders) (bs2:binders) (orig:prob) (wl:worklist)
                  (rhs:worklist -> binders -> Env.env -> list<subst_elt> -> (prob * worklist)) : solution =

   if debug env <| Options.Other "Rel"
   then BU.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                       (Print.binders_to_string ", " bs1)
                       (rel_to_string (p_rel orig))
                       (Print.binders_to_string ", " bs2);

   let rec aux wl scope env subst (xs:binders) (ys:binders) : either<(probs * formula), string> * worklist =
        match xs, ys with
        | [], [] ->
          let rhs_prob, wl = rhs wl scope env subst in
          if debug env <| Options.Other "Rel"
          then BU.print1 "rhs_prob = %s\n" (prob_to_string env rhs_prob);
          let formula = p_guard rhs_prob in
          Inl ([rhs_prob], formula), wl

        | (hd1, imp)::xs, (hd2, imp')::ys when (U.eq_aqual imp imp' = U.Equal) ->
           let hd1 = {hd1 with sort=Subst.subst subst hd1.sort} in //open both binders
           let hd2 = {hd2 with sort=Subst.subst subst hd2.sort} in
           let prob, wl = mk_t_problem wl scope orig hd1.sort (invert_rel <| p_rel orig) hd2.sort None "Formal parameter" in
           let hd1 = freshen_bv hd1 in
           let subst = DB(0, hd1)::SS.shift_subst 1 subst in  //extend the substitution
           let env = Env.push_bv env hd1 in
           begin
           match aux wl (scope @ [(hd1, imp)]) env subst xs ys with
           | Inl (sub_probs, phi), wl ->
             let phi =
                 U.mk_conj (p_guard prob)
                           (close_forall env [(hd1,imp)] phi) in
             if debug env <| Options.Other "Rel"
             then BU.print2 "Formula is %s\n\thd1=%s\n" (Print.term_to_string phi) (Print.bv_to_string hd1);
             Inl (prob::sub_probs, phi), wl

           | fail -> fail
           end

        | _ -> Inr "arity or argument-qualifier mismatch", wl in

   match aux wl [] env [] bs1 bs2 with
   | Inr msg, wl -> giveup env msg orig
   | Inl (sub_probs, phi), wl ->
     let wl = solve_prob orig (Some phi) [] wl in
     solve env (attempt sub_probs wl)

and try_solve_without_smt_or_else
        (env:Env.env) (wl:worklist)
        (try_solve: (Env.env -> worklist -> solution))
        (else_solve: Env.env -> worklist -> (prob * string) -> solution)
    : solution =
    let wl' = {wl with defer_ok=false;
                       smt_ok=false;
                       attempting=[];
                       wl_deferred=[];
                       wl_implicits=[]} in
    let tx = UF.new_transaction () in
    match try_solve env wl' with
    | Success (_, imps) ->
      UF.commit tx;
      let wl = {wl with wl_implicits=wl.wl_implicits@imps} in
      solve env wl
    | Failed (p,s) ->
      UF.rollback tx;
      else_solve env wl (p,s)

and solve_t (env:Env.env) (problem:tprob) (wl:worklist) : solution =
    def_check_prob "solve_t" (TProb problem);
    solve_t' env (compress_tprob wl.tcenv problem) wl

and solve_t_flex_rigid_eq env (orig:prob) wl
                              (lhs:flex_t)
                              (rhs:term)
    : solution =

    let binders_as_bv_set (bs:binders) =
        FStar.Util.as_set (List.map fst bs)
                          Syntax.order_bv
    in

    let mk_solution env (lhs:flex_t) (bs:binders) (rhs:term) =
        let (_, ctx_u, _) = lhs in
        let sol =
          match bs with
          | [] -> rhs
          | _ ->
            u_abs ctx_u.ctx_uvar_typ (sn_binders env bs) rhs
        in
        [TERM(ctx_u, sol)]
    in

    let try_quasi_pattern (orig:prob) (env:Env.env) (wl:worklist)
                          (lhs:flex_t) (rhs:term)
        : either<string, list<uvi>> * worklist =
        match quasi_pattern env lhs with
        | None ->
          Inl "Not a quasi-pattern", wl

        | Some (bs, _) ->
          let (t_lhs, ctx_u, args) = lhs in
          let uvars, occurs_ok, msg = occurs_check ctx_u rhs in
          if not occurs_ok
          then Inl ("quasi-pattern, occurs-check failed: " ^ (Option.get msg)), wl
          else let fvs_lhs = binders_as_bv_set (ctx_u.ctx_uvar_binders@bs) in
               let fvs_rhs = Free.names rhs in
               if not (BU.set_is_subset_of fvs_rhs fvs_lhs)
               then Inl ("quasi-pattern, free names on the RHS are not included in the LHS"), wl
               else Inr (mk_solution env lhs bs rhs), restrict_all_uvars ctx_u uvars wl
    in

    let imitate_app (orig:prob) (env:Env.env) (wl:worklist)
                    (lhs:flex_t) (bs_lhs:binders) (t_res_lhs:term)
                    (rhs:term)
        : solution =
        //if Env.debug env <| Options.Other "Rel"
        //then printfn "imitate_app 1:\n\tlhs=%s\n\tbs_lhs=%s\n\tt_res_lhs=%s\n\trhs=%s\n"
        //    (flex_t_to_string lhs)
        //    (Print.binders_to_string ", " bs_lhs)
        //    (Print.term_to_string t_res_lhs)
        //    (Print.term_to_string rhs);
        let rhs_hd, args = U.head_and_args rhs in
        let args_rhs, last_arg_rhs = BU.prefix args in
        let rhs' = S.mk_Tm_app rhs_hd args_rhs None rhs.pos in
        //if Env.debug env <| Options.Other "Rel"
        //then printfn "imitate_app 2:\n\trhs'=%s\n\tlast_arg_rhs=%s\n"
        //            (Print.term_to_string rhs')
        //            (Print.args_to_string [last_arg_rhs]);
        let t_lhs, u_lhs, _lhs_args = lhs in
        let lhs', lhs'_last_arg, wl =
              let _, t_last_arg, wl = copy_uvar u_lhs [] (fst <| U.type_u()) wl in
              //FIXME: this may be an implicit arg ... fix qualifier
              let _, lhs', wl = copy_uvar u_lhs (bs_lhs@[S.null_binder t_last_arg]) t_res_lhs wl in
              let _, lhs'_last_arg, wl = copy_uvar u_lhs bs_lhs t_last_arg wl in
              lhs', lhs'_last_arg, wl
        in
        //if Env.debug env <| Options.Other "Rel"
        //then printfn "imitate_app 3:\n\tlhs'=%s\n\tlast_arg_lhs=%s\n"
        //            (Print.term_to_string lhs')
        //            (Print.term_to_string lhs'_last_arg);
        let sol = [TERM(u_lhs, U.abs bs_lhs (S.mk_Tm_app lhs' [S.as_arg lhs'_last_arg] None t_lhs.pos)
                                            (Some (U.residual_tot t_res_lhs)))]
        in
        let sub_probs, wl =
            let p1, wl = mk_t_problem wl [] orig lhs' EQ rhs' None "first-order lhs" in
            let p2, wl = mk_t_problem wl [] orig lhs'_last_arg EQ (fst last_arg_rhs) None "first-order rhs" in
            [p1; p2], wl
        in
        solve env (attempt sub_probs (solve_prob orig None sol wl))
    in

    let first_order (orig:prob) (env:Env.env) (wl:worklist)
                    (lhs:flex_t) (rhs:term)
        : solution =
        let is_app rhs =
           let _, args = U.head_and_args rhs in
           match args with
           | [] -> false
           | _ -> true
        in
        let is_arrow rhs =
            match (SS.compress rhs).n with
            | Tm_arrow _ -> true
            | _ -> false
        in
        match quasi_pattern env lhs with
        | None ->
           giveup_or_defer env orig wl
              (BU.format1 "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                          (prob_to_string env orig))

        | Some (bs_lhs, t_res_lhs) ->
          if is_app rhs
          then imitate_app orig env wl lhs bs_lhs t_res_lhs rhs
          else if is_arrow rhs
          then imitate_arrow orig env wl lhs bs_lhs t_res_lhs EQ rhs
          else giveup_or_defer env orig wl
                               (BU.format1 "first_order heursitic cannot solve %s; \
                                            rhs not an app or arrow"
                                            (prob_to_string env orig))
    in

    match p_rel orig with
    | SUB
    | SUBINV ->
      if wl.defer_ok
      then giveup_or_defer env orig wl "flex-rigid subtyping"
      else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs

    | EQ ->
      let (_t1, ctx_uv, args_lhs) = lhs in
      match pat_vars env ctx_uv.ctx_uvar_binders args_lhs with
      | Some lhs_binders -> //Pattern
        let rhs = sn env rhs in
        let names_to_string fvs =
            List.map Print.bv_to_string (BU.set_elements fvs) |> String.concat ", "
        in
        let fvs1 = binders_as_bv_set (ctx_uv.ctx_uvar_binders @ lhs_binders) in
        let fvs2 = Free.names rhs in
        let uvars, occurs_ok, msg = occurs_check ctx_uv rhs in
        if not occurs_ok
        then giveup_or_defer env orig wl ("occurs-check failed: " ^ (Option.get msg))
        else if BU.set_is_subset_of fvs2 fvs1
        then let sol = mk_solution env lhs lhs_binders rhs in
             let wl = restrict_all_uvars ctx_uv uvars wl in
             solve env (solve_prob orig None sol wl)
        else if wl.defer_ok
        then giveup_or_defer env orig wl
                             (BU.format3 "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                              (names_to_string fvs2)
                                              (names_to_string fvs1)
                                              (Print.binders_to_string ", " (ctx_uv.ctx_uvar_binders @ lhs_binders)))
        else first_order orig env wl lhs rhs


      | _ -> //Not a pattern
        if wl.defer_ok
        then giveup_or_defer env orig wl "Not a pattern"
        else match try_quasi_pattern orig env wl lhs rhs with
            | Inr sol, wl ->
              solve env (solve_prob orig None sol wl)
            | Inl msg, _ -> //try first-order
              first_order orig env wl lhs rhs

(* solve_t_flex-flex:
       Always delay flex-flex constraints, if possible.
       If not, coerce both sides to patterns and solve
*)
and solve_t_flex_flex env orig wl (lhs:flex_t) (rhs:flex_t) : solution =
    match p_rel orig with
    | SUB
    | SUBINV ->
      if wl.defer_ok
      then giveup_or_defer env orig wl "flex-flex subtyping"
      else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs

    | EQ ->
      if wl.defer_ok
      && (not (is_flex_pat lhs)|| not (is_flex_pat rhs))
      then giveup_or_defer env orig wl "flex-flex non-pattern"
      else
          match quasi_pattern env lhs, quasi_pattern env rhs with
          | Some (binders_lhs, t_res_lhs), Some (binders_rhs, t_res_rhs) ->
            let ({pos=range}, u_lhs, _) = lhs in
            let (_, u_rhs, _) = rhs in
            if UF.equiv u_lhs.ctx_uvar_head u_rhs.ctx_uvar_head
            && binders_eq binders_lhs binders_rhs
            then solve env (solve_prob orig None [] wl)
            else (* Given a flex-flex instance:
                    (x1..xn ..X  |- ?u : ts  -> tres) [y1  ... ym ]
                 ~  (x1..xn ..X'| - ?v : ts' -> tres) [y1' ... ym']

                    let ctx_w = x1..xn in
                    let z1..zk = (..X..y1..ym intersect ...X'...y1'..ym') in
                    (ctx_w |- ?w : z1..zk -> tres) [z1..zk]

                    ?u := (fun y1..ym -> ?w z1...zk)
                    ?v := (fun y1'..ym' -> ?w z1...zk)
                 *)
                 //let sub_prob, wl =
                 //   //is it strictly necessary to add this sub problem?
                 //   //we don't in other cases
                 //     mk_t_problem wl [] orig t_res_lhs EQ t_res_rhs None "flex-flex typing"
                 //in
                 let ctx_w, (ctx_l, ctx_r) =
                    maximal_prefix u_lhs.ctx_uvar_binders
                                   u_rhs.ctx_uvar_binders
                 in
                 let gamma_w = gamma_until u_lhs.ctx_uvar_gamma ctx_w in
                 let zs = intersect_binders gamma_w (ctx_l @ binders_lhs) (ctx_r @ binders_rhs) in
                 let _, w, wl = new_uvar ("flex-flex quasi:"
                                          ^"\tlhs="  ^u_lhs.ctx_uvar_reason
                                          ^ "\trhs=" ^u_rhs.ctx_uvar_reason)
                                         wl range gamma_w ctx_w (U.arrow zs (S.mk_Total t_res_lhs))
                                         Strict in
                 let w_app = S.mk_Tm_app w (List.map (fun (z, _) -> S.as_arg (S.bv_to_name z)) zs) None w.pos in
                 let _ =
                    if Env.debug env <| Options.Other "Rel"
                    then BU.print "flex-flex quasi:\n\t\
                                        lhs=%s\n\t\
                                        rhs=%s\n\t\
                                        sol=%s\n\t\
                                        ctx_l@binders_lhs=%s\n\t\
                                        ctx_r@binders_rhs=%s\n\t\
                                        zs=%s\n"
                            [flex_t_to_string lhs;
                             flex_t_to_string rhs;
                             term_to_string w;
                             Print.binders_to_string ", " (ctx_l@binders_lhs);
                             Print.binders_to_string ", " (ctx_r@binders_rhs);
                             Print.binders_to_string ", " zs]
                 in
                 let sol =
                     let s1 = TERM(u_lhs, U.abs binders_lhs w_app (Some (U.residual_tot t_res_lhs))) in
                     if Unionfind.equiv u_lhs.ctx_uvar_head u_rhs.ctx_uvar_head
                     then [s1]
                     else let s2 = TERM(u_rhs, U.abs binders_rhs w_app (Some (U.residual_tot t_res_lhs))) in
                          [s1;s2]
                 in
                 solve env (solve_prob orig None sol wl)

          | _ ->
            giveup_or_defer env orig wl "flex-flex: non-patterns"

and solve_t' (env:Env.env) (problem:tprob) (wl:worklist) : solution =
    def_check_prob "solve_t'.1" (TProb problem);
    let giveup_or_defer orig msg = giveup_or_defer env orig wl msg in

    let rigid_heads_match (env:Env.env) (need_unif:bool) (torig:tprob) (wl:worklist) (t1:term) (t2:term) : solution =
        let orig = TProb torig in
        if debug env <| Options.Other "Rel"
        then BU.print5 "Heads %s: %s (%s) and %s (%s)\n"
            (if need_unif then "need unification" else "match")
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
        else
        if nargs=0 || U.eq_args args1 args2=U.Equal //special case: for easily proving things like nat <: nat, or greater_than i <: greater_than i etc.
        then if need_unif
             then solve_t env ({problem with lhs=head1; rhs=head2}) wl
             else match solve_maybe_uinsts env orig head1 head2 wl with
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
            let base1, refinement1 = base_and_refinement env t1 in
            let base2, refinement2 = base_and_refinement env t2 in
            begin
            match refinement1, refinement2 with
            | None, None ->  //neither side is a refinement; reason extensionally
              let argp = List.zip ((head1, None)::args1) ((head2, None)::args2) in
              let mk_sub_probs wl =
                   let subprobs, wl =
                        List.fold_right
                            (fun ((a1, _), (a2, _)) (probs, wl) ->
                               let prob', wl = mk_problem wl (p_scope orig) orig a1 EQ a2 None "index" in
                               (TProb prob')::probs, wl)
                             argp
                             ([], wl)
                   in
                   if debug env <| Options.Other "Rel"
                   then BU.print1
                            "Adding subproblems for arguments: %s"
                            (Print.list_to_string (prob_to_string env) subprobs);
                   if Options.defensive ()
                   then List.iter (def_check_prob "solve_t' subprobs") subprobs;
                   subprobs, wl
              in
              let solve_sub_probs env wl =
                  let subprobs, wl = mk_sub_probs wl in
                  let formula = U.mk_conj_l (List.map (fun p -> p_guard p) subprobs) in
                  let wl = solve_prob orig (Some formula) [] wl in
                  solve env (attempt subprobs wl)
              in
              let solve_sub_probs_no_smt env wl =
                  let subprobs, wl = mk_sub_probs wl in
                  let wl = solve_prob orig None [] wl in
                  solve env (attempt subprobs wl)
              in
              let unfold_and_retry d env wl (prob, reason) =
                  if debug env <| Options.Other "Rel"
                  then BU.print2 "Failed to solve %s without SMT because %s"
                                (prob_to_string env prob)
                                reason;
                   let t1' = normalize_refinement [Env.UnfoldUntil d; Env.Weak; Env.HNF] env t1 in
                   let t2' = normalize_refinement [Env.UnfoldUntil d; Env.Weak; Env.HNF] env t2 in
                   let head1', _ = U.head_and_args t1' in
                   let head2', _ = U.head_and_args t2' in
                   match U.eq_tm head1' head1, U.eq_tm head2' head2 with
                   | U.Equal, U.Equal -> //unfolding didn't make progress
                      if debug env <| Options.Other "Rel"
                      then BU.print4
                            "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                (Print.term_to_string t1)
                                (Print.term_to_string t1')
                                (Print.term_to_string t2)
                                (Print.term_to_string t2');
                     solve_sub_probs env wl //fallback to trying to solve with SMT on
                   | _ -> solve_t env ({torig with lhs=t1'; rhs=t2'}) wl
              in
              let d =
                match delta_depth_of_term env head1 with
                | None -> None
                | Some d -> decr_delta_depth d
              in
              begin
              match d with
              | Some d when wl.smt_ok ->
                try_solve_without_smt_or_else env wl
                    solve_sub_probs_no_smt
                    (unfold_and_retry d)

              | _ -> //cannot be unfolded or no smt anyway; so just try to solve extensionally
                if debug env <| Options.Other "Rel"
                then BU.print3
                    "Cannot unfold %s or %s since delta_depth=%s\n"
                                (Print.term_to_string t1)
                                (Print.term_to_string t2)
                                (match d with | None -> "None" | Some d -> Print.delta_depth_to_string d);
                solve_sub_probs env wl

              end




              //if need_unif then
              //    let argp = List.zip ((head1, None)::args1) ((head2, None)::args2) in
              //    let subprobs, wl = List.fold_right (fun ((a1, _), (a2, _)) (probs, wl) ->
              //                          let prob', wl = mk_problem wl (p_scope orig) orig a1 EQ a2 None "index" in
              //                          (TProb prob')::probs, wl) argp ([], wl)
              //    in
              //    if debug env <| Options.Other "Rel" then
              //        BU.print1 "Adding subproblems for arguments: %s" (Print.list_to_string (prob_to_string env) subprobs);
              //    let formula = U.mk_conj_l (List.map (fun p -> p_guard p) subprobs) in
              //    let wl = solve_prob orig (Some formula) [] wl in
              //    solve env (attempt subprobs wl)
              //else begin
              //     match solve_maybe_uinsts env orig head1 head2 wl with
              //     | UFailed msg -> giveup env msg orig
              //     | UDeferred wl -> solve env (defer "universe constraints" orig wl)
              //     | USolved wl ->
              //       let subprobs, wl =
              //         List.fold_right2
              //           (fun (a, _) (a', _) (subprobs, wl) ->
              //               let p, wl = mk_t_problem wl [] orig a EQ a' None "index" in
              //               p::subprobs, wl)
              //           args1
              //           args2
              //           ([], wl)
              //       in
              //       if debug env <| Options.Other "Rel"
              //       then BU.print1 "Adding subproblems for arguments: %s\n"
              //                      (Print.list_to_string (prob_to_string env) subprobs);

              //       List.iter (def_check_prob "solve_t' subprobs") subprobs;
              //       let formula = U.mk_conj_l (List.map p_guard subprobs) in
              //       let wl = solve_prob orig (Some formula) [] wl in
              //       solve env (attempt subprobs wl)
              //     end

            | _ ->
              let lhs = force_refinement (base1, refinement1) in
              let rhs = force_refinement (base2, refinement2) in
              solve_t env ({problem with lhs=lhs; rhs=rhs}) wl
            end
    in

    (* <try_match_heuristic>:
          (match ?u with P1 -> t1 | ... | Pn -> tn) ~ t

          when (head t) `matches` (head ti)
          solve ?u to Pi
          and then try to prove `t ~ ti`
     *)
    let try_match_heuristic env orig wl s1 s2 t1t2_opt =
        let try_solve_branch scrutinee p =
            let (_t, uv, _args), wl = destruct_flex_t scrutinee wl  in
            let xs, pat_term, _, _ = PatternUtils.pat_as_exp true env p in
            let subst, wl =
                List.fold_left (fun (subst, wl) x ->
                    let t_x = SS.subst subst x.sort in
                    let _, u, wl = copy_uvar uv [] t_x wl in
                    let subst = NT(x, u)::subst in
                    subst, wl)
                    ([], wl)
                    xs
            in
            let pat_term = SS.subst subst pat_term in
            let prob, wl =
                new_problem wl env scrutinee
                            EQ pat_term None scrutinee.pos
                            "match heuristic"
            in
            let wl' = {wl with defer_ok=false;
                                smt_ok=false;
                                attempting=[TProb prob];
                                wl_deferred=[];
                                wl_implicits=[]} in
            let tx = UF.new_transaction () in
            match solve env wl' with
            | Success (_, imps) ->
                let wl' = {wl' with attempting=[orig]} in
                (match solve env wl' with
                | Success (_, imps') ->
                  UF.commit tx;
                  Some ({wl with wl_implicits=wl.wl_implicits@imps@imps'})

                | Failed _ ->
                  UF.rollback tx;
                  None)
            | _ ->
              UF.rollback tx;
              None
        in
        match t1t2_opt with
        | None -> Inr None
        | Some (t1, t2) ->
            if Env.debug env <| Options.Other "Rel"
            then BU.print2 "Trying match heuristic for %s vs. %s\n"
                            (Print.term_to_string t1)
                            (Print.term_to_string t2);
            match (s1, U.unmeta t1), (s2, U.unmeta t2) with
            | (_, {n=Tm_match (scrutinee, branches)}), (s, t)
            | (s, t), (_, {n=Tm_match(scrutinee, branches)}) ->
              if not (is_flex scrutinee)
              then begin
                if Env.debug env <| Options.Other "Rel"
                then BU.print1 "match head %s is not a flex term\n" (Print.term_to_string scrutinee);
                Inr None
              end
              else if wl.defer_ok
              then (if Env.debug env <| Options.Other "Rel"
                    then BU.print_string "Deferring ... \n";
                    Inl "defer")
              else begin
                  if Env.debug env <| Options.Other "Rel"
                  then BU.print2 "Heuristic applicable with scrutinee %s and other side = %s\n"
                                (Print.term_to_string scrutinee)
                                (Print.term_to_string t);
                  let pat_discriminates = function
                      | ({v=Pat_constant _}, None, _)
                      | ({v=Pat_cons _}, None, _) -> true
                      | _ -> false //other patterns do not discriminate
                  in
                  let head_matching_branch =
                      branches |>
                      BU.try_find
                          (fun b ->
                            if pat_discriminates b
                            then
                              let (_, _, t') = SS.open_branch b in
                              match head_matches_delta env s t' with
                              | FullMatch, _
                              | HeadMatch _, _ ->
                                true
                              | _ -> false
                            else false)
                  in
                  begin
                  match head_matching_branch with
                  | None ->
                    if Env.debug env <| Options.Other "Rel"
                    then BU.print_string "No head_matching branch\n";
                    let try_branches =
                        match BU.prefix_until (fun b -> not (pat_discriminates b)) branches with
                        | Some (branches, _, _) -> branches
                        | _ -> branches
                    in
                    Inr <| BU.find_map try_branches (fun b ->
                        let (p, _, _) = SS.open_branch b in
                        try_solve_branch scrutinee p)

                  | Some b ->
                    let (p, _, e) = SS.open_branch b in
                    if Env.debug env <| Options.Other "Rel"
                    then BU.print2 "Found head matching branch %s -> %s\n"
                                (Print.pat_to_string p)
                                (Print.term_to_string e);
                    Inr <| try_solve_branch scrutinee p

                  end
              end
            | _ ->
              if Env.debug env <| Options.Other "Rel"
              then BU.print2 "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                    (Print.tag_of_term t1) (Print.tag_of_term t2);
              Inr None
    in

    (* <rigid_rigid_delta>: are t1 and t2, with head symbols head1 and head2, compatible after some delta steps? *)
    let rigid_rigid_delta (env:Env.env) (torig:tprob) (wl:worklist)
                          (head1:term) (head2:term) (t1:term) (t2:term)
        : solution =
        let orig = TProb torig in
        if Env.debug env <| Options.Other "RelDelta" then
            BU.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                        (Print.tag_of_term t1)
                        (Print.tag_of_term t2)
                        (Print.term_to_string t1)
                        (Print.term_to_string t2);
        let m, o = head_matches_delta env t1 t2 in
        match m, o  with
        | (MisMatch _, _) -> //heads definitely do not match
            let rec may_relate head =
                match (SS.compress head).n with
                | Tm_name _
                | Tm_match _ -> true
                | Tm_fvar fv ->
                    (match Env.delta_depth_of_fv env fv with
                     | Delta_equational_at_level _ ->
                       true
                     | Delta_abstract _ ->
                        //these may be relatable via a logical theory
                        //which may provide **equations** among abstract symbols
                        //Note, this is specifically not applicable for subtyping queries: see issue #1359
                       problem.relation = EQ
                    | _ -> false)
                | Tm_ascribed (t, _, _)
                | Tm_uinst (t, _)
                | Tm_meta (t, _) -> may_relate t
                | _ -> false
            in
            begin
            match try_match_heuristic env orig wl t1 t2 o with
            | Inl _defer_ok ->
              giveup_or_defer orig "delaying match heuristic"

            | Inr (Some wl) ->
              solve env wl

            | Inr None ->
                if (may_relate head1 || may_relate head2) && wl.smt_ok
                then let guard, wl = guard_of_prob env wl problem t1 t2 in
                    solve env (solve_prob orig (Some guard) [] wl)
                else giveup env (BU.format4 "head mismatch (%s (%s) vs %s (%s))"
                                                  (Print.term_to_string head1)
                                                  (BU.dflt ""
                                                    (BU.bind_opt (delta_depth_of_term env head1)
                                                                 (fun x -> Some (Print.delta_depth_to_string x))))
                                                  (Print.term_to_string head2)
                                                  (BU.dflt ""
                                                    (BU.bind_opt (delta_depth_of_term env head2)
                                                                (fun x -> Some (Print.delta_depth_to_string x))))
                                                  ) orig
            end

        | (HeadMatch true, _) when problem.relation <> EQ ->
            //heads may only match after unification;
            //but we're not trying to unify them here
            //so, treat as a mismatch
            if wl.smt_ok
            then let guard, wl = guard_of_prob env wl problem t1 t2 in
                    solve env (solve_prob orig (Some guard) [] wl)
            else giveup env (BU.format2 "head mismatch for subtyping (%s vs %s)"
                                        (Print.term_to_string t1)
                                        (Print.term_to_string t2))
                                orig

        | (_, Some (t1, t2)) -> //heads match after some delta steps
            solve_t env ({problem with lhs=t1; rhs=t2}) wl

        (* Need to maybe reunify the heads *)
        | (HeadMatch unif, None) ->
            rigid_heads_match env unif torig wl t1 t2

        | (FullMatch, None) ->
            rigid_heads_match env false torig wl t1 t2
    in
    (* <rigid_rigid_delta> *)

    let orig = TProb problem in
    def_check_prob "solve_t'.2" orig;
    if BU.physical_equality problem.lhs problem.rhs then solve env (solve_prob orig None [] wl) else
    let t1 = problem.lhs in
    let t2 = problem.rhs in
    def_check_closed_in (p_loc orig) "ref.t1" (List.map fst (p_scope orig)) t1;
    def_check_closed_in (p_loc orig) "ref.t2" (List.map fst (p_scope orig)) t2;
    let _ =
        if debug env (Options.Other "Rel")
        then BU.print3 "Attempting %s (%s vs %s)\n" (string_of_int problem.pid)
                            (Print.tag_of_term t1 ^ "::" ^ Print.term_to_string t1)
                            (Print.tag_of_term t2 ^ "::" ^ Print.term_to_string t2)
                            in
    let r = Env.get_range env in
    match t1.n, t2.n with
      | Tm_delayed _, _
      | _, Tm_delayed _ ->
        // GM: I imagine there is some reason these terms are always
        // compressed, since the original code didn't call compress and
        // it never failed. Adding surely implies a performance hit, so
        // I didn't do that, but it'd be nice to document the reason
        // this works (I couldn't figure it out).

        // NS: we reach this point only after call compress_tprob
        //     or something that does a compress already, e.g., unascribe, or unmeta etc.
        //     See all the callers to solve_t'
        failwith "Impossible: terms were not compressed"

      | Tm_ascribed _, _ ->
        solve_t' env ({problem with lhs=U.unascribe t1}) wl

      | Tm_meta _, _ ->
        solve_t' env ({problem with lhs=U.unmeta t1}) wl

      | _, Tm_ascribed _ ->
        solve_t' env ({problem with rhs=U.unascribe t2}) wl

      | _, Tm_meta _ ->
        solve_t' env ({problem with rhs=U.unmeta t2}) wl

      | Tm_quoted (t1, _), Tm_quoted (t2, _) ->
        (* solve_prob orig None [] wl *)
        solve env (solve_prob orig None [] wl)
        (* solve_t' env ({problem with lhs = t1; rhs = t2}) wl *)

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
        (fun wl scope env subst  ->
            let c1 = Subst.subst_comp subst c1 in
            let c2 = Subst.subst_comp subst c2 in //open both comps
            let rel = if (Options.use_eq_at_higher_order()) then EQ else problem.relation in
            mk_c_problem wl scope orig c1 rel c2 None "function co-domain")

      | Tm_abs(bs1, tbody1, lopt1), Tm_abs(bs2, tbody2, lopt2) ->
        let mk_t t l = function
            | [] -> t
            | bs -> mk (Tm_abs(bs, t, l)) None t.pos in
        let (bs1, tbody1), (bs2, tbody2) =
            match_num_binders (bs1, mk_t tbody1 lopt1) (bs2, mk_t tbody2 lopt2) in
        solve_binders env bs1 bs2 orig wl
        (fun wl scope env subst ->
           mk_t_problem wl scope orig (Subst.subst subst tbody1)
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
                 if is_abs t then Inl t else Inr t
        in
        let force_eta t =
            if is_abs t then t
            else let _, ty, _ = env.type_of ({env with lax=true; use_bv_sorts=true; expected_typ=None}) t in
                 N.eta_expand_with_type env t (N.unfold_whnf env ty)
        in
        begin
            match maybe_eta t1, maybe_eta t2 with
            | Inl t1, Inl t2 ->
              solve_t env ({problem with lhs=t1; rhs=t2}) wl
            | Inl t_abs, Inr not_abs
            | Inr not_abs, Inl t_abs ->
              //we lack the type information to eta-expand properly
              //so, this is going to fail, except if one last shot succeeds
              if is_flex not_abs //if it's a pattern and the free var check succeeds, then unify it with the abstraction in one step
              && p_rel orig = EQ
              then let flex, wl = destruct_flex_t not_abs wl in
                    solve_t_flex_rigid_eq env orig wl flex t_abs
              else let t1 = force_eta t1 in
                   let t2 = force_eta t2 in
                   if is_abs t1 && is_abs t2
                   then solve_t env ({problem with lhs=t1; rhs=t2}) wl
                   else giveup env "head tag mismatch: RHS is an abstraction" orig
            | _ -> failwith "Impossible: at least one side is an abstraction"
        end

      | Tm_refine(x1, phi1), Tm_refine(x2, phi2) ->
        (* If the heads of their bases can match, make it so, and continue *)
        (* The unfolding is very much needed since we might have
         *   n:nat{phi n} =?= i:int{psi i}
         * and if we try to unify the bases, nat and int, we're toast.
         * However too much unfolding is also harmful for inference! See
         * the discussion on #1345. Hence we reuse head_matches_delta to
         * do the unfolding for us, which is good *heuristic* but not
         * necessarily always correct.
         *)
        let x1, x2 =
            match head_matches_delta env x1.sort x2.sort with
            (* We allow (HeadMatch true) since we're gonna unify them again anyway via base_prob *)
            | FullMatch, Some (t1, t2)
            | HeadMatch _, Some (t1, t2) ->
                ({ x1 with sort = t1 }), ({ x2 with sort = t2 })
            | _ -> x1, x2
        in
        (* A bit hackish *)
        let t1 = U.refine x1 phi1 in
        let t2 = U.refine x2 phi2 in
        (* / hack *)
        let x1, phi1 = as_refinement false env t1 in
        let x2, phi2 = as_refinement false env t2 in
        if Env.debug env (Options.Other "Rel") then begin
            BU.print3 "ref1 = (%s):(%s){%s}\n" (Print.bv_to_string x1)
                                               (Print.term_to_string x1.sort)
                                               (Print.term_to_string phi1);
            BU.print3 "ref2 = (%s):(%s){%s}\n" (Print.bv_to_string x2)
                                               (Print.term_to_string x2.sort)
                                               (Print.term_to_string phi2)
        end;
        let base_prob, wl = mk_t_problem wl [] orig x1.sort problem.relation x2.sort problem.element "refinement base type" in
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
                let guard = U.mk_conj (p_guard base_prob) impl in
                def_check_closed_in (p_loc orig) "ref.1" (List.map fst (p_scope orig)) (p_guard base_prob);
                def_check_closed_in (p_loc orig) "ref.2" (List.map fst (p_scope orig)) impl;
                let wl = solve_prob orig (Some guard) [] wl in
                solve env (attempt [base_prob] wl)
             in
        let has_uvars =
            not (BU.set_is_empty (FStar.Syntax.Free.uvars phi1))
            || not (BU.set_is_empty (FStar.Syntax.Free.uvars phi2))
        in
        if problem.relation = EQ
        || (not env.uvar_subtyping && has_uvars)
        then let ref_prob, wl =
                  mk_t_problem wl [mk_binder x1] orig phi1 EQ phi2 None "refinement formula"
             in
             match solve env ({wl with defer_ok=false; attempting=[ref_prob]; wl_deferred=[]}) with
             | Failed (prob, msg) ->
               if (not env.uvar_subtyping && has_uvars)
               || not wl.smt_ok
               then giveup env msg prob
               else fallback()

             | Success _ ->
               let guard =
                   U.mk_conj (p_guard base_prob)
                             (p_guard ref_prob |> guard_on_element wl problem x1) in
               let wl = solve_prob orig (Some guard) [] wl in
               let wl = {wl with ctr=wl.ctr+1} in
               solve env (attempt [base_prob] wl)
        else fallback()

      (* flex-flex *)
      | Tm_uvar _,                Tm_uvar _
      | Tm_app({n=Tm_uvar _}, _), Tm_uvar _
      | Tm_uvar _,                Tm_app({n=Tm_uvar _}, _)
      | Tm_app({n=Tm_uvar _}, _), Tm_app({n=Tm_uvar _}, _) ->
        let f1, wl = destruct_flex_t t1 wl in
        let f2, wl = destruct_flex_t t2 wl in
        solve_t_flex_flex env orig wl f1 f2

      (* flex-rigid equalities *)
      | Tm_uvar _, _
      | Tm_app({n=Tm_uvar _}, _), _ when (problem.relation=EQ) -> (* just imitate/project ... no slack *)
        let f1, wl = destruct_flex_t t1 wl in
        solve_t_flex_rigid_eq env orig wl f1 t2

      (* rigid-flex: reorient if it is an equality constraint *)
      | _, Tm_uvar _
      | _, Tm_app({n=Tm_uvar _}, _) when (problem.relation = EQ) ->
        solve_t env (invert problem) wl

      (* flex-rigid: ?u _ <: t1 -> t2 *)
      | Tm_uvar _, Tm_arrow _
      | Tm_app({n=Tm_uvar _}, _), Tm_arrow _ ->
        //FIXME! This is weird; it should be handled by imitate_arrow
        //this case is so common, that even though we could delay, it is almost always ok to solve it immediately as an equality
        //besides, in the case of arrows, if we delay it, the arity of various terms built by the unifier goes awry
        //so, don't delay!
        solve_t' env ({problem with relation=EQ}) wl

      | _, Tm_uvar _
      | _, Tm_app({n=Tm_uvar _}, _)
      | Tm_uvar _, _
      | Tm_app({n=Tm_uvar _}, _), _ ->
        //flex-rigid subtyping is handled in the top-loop
        solve env (attempt [TProb problem] wl)

      | Tm_refine _, _ ->
        let t2 = force_refinement <| base_and_refinement env t2 in
        solve_t env ({problem with rhs=t2}) wl

      | _, Tm_refine _ ->
        let t1 = force_refinement <| base_and_refinement env t1 in
        solve_t env ({problem with lhs=t1}) wl

      | Tm_match (s1, brs1), Tm_match (s2, brs2) ->
        let by_smt () =
            // using original WL
            let guard, wl = guard_of_prob env wl problem t1 t2 in
            solve env (solve_prob orig (Some guard) [] wl)
        in
        let rec solve_branches wl brs1 brs2 : option<(list<prob> * worklist)> =
            match brs1, brs2 with
            | br1::rs1, br2::rs2 ->
                let (p1, w1, _) = br1 in
                let (p2, w2, _) = br2 in
                (* If the patterns differ in shape, just fail *)
                if not (eq_pat p1 p2) then None else

                (* Open the first branch, and use that same substitution for the second branch *)
                let (p1, w1, e1), s = SS.open_branch' br1 in
                let (p2, w2, e2) = br2 in
                let w2 = BU.map_opt w2 (SS.subst s) in
                let e2 = SS.subst s e2 in

                let scope = List.map S.mk_binder <| S.pat_bvs p1 in

                (* Subproblem for then `when` clause *)
                BU.bind_opt (
                    match w1, w2 with
                    | Some _, None
                    | None, Some _ -> None
                    | None, None -> Some ([], wl)
                    | Some w1, Some w2 ->
                        let p, wl = mk_t_problem wl scope orig w1 EQ w2 None "when clause" in
                        Some ([p], wl))
                (fun (wprobs, wl) ->

                (* Branch body *)
                // GM: Could use problem.relation here instead of EQ?
                let prob, wl = mk_t_problem wl scope orig e1 EQ e2 None "branch body" in
                BU.bind_opt (solve_branches wl rs1 rs2) (fun (r, wl) ->
                Some (prob::(wprobs @ r), wl)))

            | [], [] -> Some ([], wl)
            | _ -> None
        in
        begin match solve_branches wl brs1 brs2 with
        | None ->
            if wl.smt_ok
            then by_smt ()
            else giveup env "Tm_match branches don't match" orig
        | Some (sub_probs, wl) ->
            let sc_prob, wl = mk_t_problem wl [] orig s1 EQ s2 None "match scrutinee" in
            let sub_probs = sc_prob::sub_probs in
            let formula = U.mk_conj_l (List.map (fun p -> p_guard p) sub_probs) in
            let tx = UF.new_transaction () in
            let wl = solve_prob orig (Some formula) [] wl in
            begin match solve env (attempt sub_probs ({wl with smt_ok = false})) with
            | Success (ds, imp) ->
                UF.commit tx;
                Success (ds, imp)
            | Failed _ ->
                UF.rollback tx;
                by_smt ()
            end
        end

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
         let _ =
             if debug env (Options.Other "Rel")
             then BU.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" (string_of_int problem.pid)
                                 (Print.term_to_string head1)
                                 (Print.term_to_string head2)
         in
         let no_free_uvars t = BU.set_is_empty (Free.uvars t) && BU.set_is_empty (Free.univs t) in
         let equal t1 t2 =
            let t1 = N.normalize [Env.UnfoldUntil delta_constant; Env.Primops; Env.Beta; Env.Eager_unfolding; Env.Iota] env t1 in
            let t2 = N.normalize [Env.UnfoldUntil delta_constant; Env.Primops; Env.Beta; Env.Eager_unfolding; Env.Iota] env t2 in
            U.eq_tm t1 t2 = U.Equal
         in
         if (Env.is_interpreted env head1 || Env.is_interpreted env head2) //we have something like (+ x1 x2) =?= (- y1 y2)
           && problem.relation = EQ
           && wl.smt_ok // with SMT allowed
           && no_free_uvars t1 // and neither term has any free variables
           && no_free_uvars t2
         then let guard, wl =
                  if equal t1 t2
                  then None, wl
                  else let g, wl = mk_eq2 wl orig t1 t2 in
                       Some g, wl
              in
              solve env (solve_prob orig guard [] wl)
         else rigid_rigid_delta env problem wl head1 head2 t1 t2

      | Tm_let _, Tm_let _ ->
         // For now, just unify if they syntactically match
         if U.term_eq t1 t2
         then solve env (solve_prob orig None [] wl)
         else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig

      | Tm_let _, _
      | _, Tm_let _ ->
         raise_error (Errors.Fatal_UnificationNotWellFormed, BU.format4 "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                            (Print.tag_of_term t1) (Print.tag_of_term t2)
                            (Print.term_to_string t1) (Print.term_to_string t2)) t1.pos

      | _ -> giveup env "head tag mismatch" orig

and solve_c (env:Env.env) (problem:problem<comp>) (wl:worklist) : solution =
    let c1 = problem.lhs in
    let c2 = problem.rhs in
    let orig = CProb problem in
    let sub_prob : worklist -> term -> rel -> term -> string -> prob * worklist =
        fun wl t1 rel t2 reason -> mk_t_problem wl [] orig t1 rel t2 None reason in

    let solve_eq c1_comp c2_comp =
        let _ = if Env.debug env <| Options.Other "EQ"
                then BU.print2 "solve_c is using an equality constraint (%s vs %s)\n"
                            (Print.comp_to_string (mk_Comp c1_comp))
                            (Print.comp_to_string (mk_Comp c2_comp)) in
        if not (lid_equals c1_comp.effect_name c2_comp.effect_name)
        then giveup env (BU.format2 "incompatible effects: %s <> %s"
                                        (Print.lid_to_string c1_comp.effect_name)
                                        (Print.lid_to_string c2_comp.effect_name)) orig
        else let ret_sub_prob, wl = sub_prob wl c1_comp.result_typ EQ c2_comp.result_typ "effect ret type" in
             let arg_sub_probs, wl =
                 List.fold_right2
                        (fun (a1, _) (a2, _) (arg_sub_probs, wl) ->
                           let p, wl = sub_prob wl a1 EQ a2 "effect arg" in
                           p::arg_sub_probs, wl)
                        c1_comp.effect_args
                        c2_comp.effect_args
                        ([], wl)
             in
             let sub_probs = ret_sub_prob :: arg_sub_probs in
             let guard = U.mk_conj_l (List.map p_guard sub_probs) in
             let wl = solve_prob orig (Some guard) [] wl in
             solve env (attempt sub_probs wl)
    in

    let solve_sub c1 edge c2 =
        let r = Env.get_range env in
        let lift_c1 () =
             let wp = match c1.effect_args with
                      | [(wp1,_)] -> wp1
                      | _ -> failwith (BU.format1 "Unexpected number of indices on a normalized effect (%s)" (Range.string_of_range (range_of_lid c1.effect_name))) in
             let univs =
               match c1.comp_univs with
               | [] -> [env.universe_of env c1.result_typ]
               | x -> x in
             {
                comp_univs=univs;
                effect_name=c2.effect_name;
                result_typ=c1.result_typ;
                effect_args=[as_arg (edge.mlift.mlift_wp (List.hd univs) c1.result_typ wp)];
                flags=c1.flags
             }
        in
        if problem.relation = EQ
        then solve_eq (lift_c1 ()) c2
        else let is_null_wp_2 = c2.flags |> BU.for_some (function TOTAL | MLEFFECT | SOMETRIVIAL -> true | _ -> false) in
             let wpc1, wpc2 = match c1.effect_args, c2.effect_args with
              | (wp1, _)::_, (wp2, _)::_ -> wp1, wp2
              | _ ->
                raise_error (Errors.Fatal_ExpectNormalizedEffect, (BU.format2 "Got effects %s and %s, expected normalized effects"
                                          (Print.lid_to_string c1.effect_name)
                                          (Print.lid_to_string c2.effect_name))) env.range
             in
             if BU.physical_equality wpc1 wpc2
             then solve_t env (problem_using_guard orig c1.result_typ problem.relation c2.result_typ None "result type") wl
             else let c2_decl, qualifiers = must (Env.effect_decl_opt env c2.effect_name) in
                  if qualifiers |> List.contains Reifiable
                  then let c1_repr =
                           N.normalize [Env.UnfoldUntil delta_constant; Env.Weak; Env.HNF] env
                                       (Env.reify_comp env (S.mk_Comp (lift_c1 ())) (env.universe_of env c1.result_typ))
                       in
                       let c2_repr =
                           N.normalize [Env.UnfoldUntil delta_constant; Env.Weak; Env.HNF] env
                                       (Env.reify_comp env (S.mk_Comp c2) (env.universe_of env c2.result_typ))
                       in
                       let prob, wl =
                           sub_prob wl c1_repr problem.relation c2_repr
                                    (BU.format2 "sub effect repr: %s <: %s"
                                                    (Print.term_to_string c1_repr)
                                                    (Print.term_to_string c2_repr))
                       in
                       let wl = solve_prob orig (Some (p_guard prob)) [] wl in
                       solve env (attempt [prob] wl)
                  else
                      let g =
                         if env.lax then
                            U.t_true
                         else if is_null_wp_2
                         then let _ = if debug env <| Options.Other "Rel"
                                      then BU.print_string "Using trivial wp ... \n" in
                              let c1_univ = env.universe_of env c1.result_typ in
                              mk (Tm_app(inst_effect_fun_with [c1_univ] env c2_decl c2_decl.trivial,
                                        [as_arg c1.result_typ;
                                         as_arg <| edge.mlift.mlift_wp c1_univ c1.result_typ wpc1]))
                                 None r
                         else let c1_univ = env.universe_of env c1.result_typ in
                              let c2_univ = env.universe_of env c2.result_typ in
                               mk (Tm_app(inst_effect_fun_with
                                                [c2_univ] env c2_decl c2_decl.stronger,
                                          [as_arg c2.result_typ;
                                           as_arg wpc2;
                                           as_arg <| edge.mlift.mlift_wp c1_univ c1.result_typ wpc1]))
                                   None r in
                      if debug env <| Options.Other "Rel" then
                          BU.print1 "WP guard (simplifed) is (%s)\n" (Print.term_to_string (N.normalize [Env.Iota; Env.Eager_unfolding; Env.Primops; Env.Simplify] env g));
                      let base_prob, wl = sub_prob wl c1.result_typ problem.relation c2.result_typ "result type" in
                      let wl = solve_prob orig (Some <| U.mk_conj (p_guard base_prob) g) [] wl in
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
            || (U.is_total_comp c1 && U.is_total_comp c2)
            || (U.is_total_comp c1 && U.is_ml_comp c2 && problem.relation=SUB)
            then solve_t env (problem_using_guard orig (U.comp_result c1) problem.relation (U.comp_result c2) None "result type") wl
            else let c1_comp = Env.comp_to_comp_typ env c1 in
                 let c2_comp = Env.comp_to_comp_typ env c2 in
                 if problem.relation=EQ
                 then let c1_comp, c2_comp =
                            if lid_equals c1_comp.effect_name c2_comp.effect_name
                            then c1_comp, c2_comp
                            else Env.unfold_effect_abbrev env c1,
                                 Env.unfold_effect_abbrev env c2 in
                      solve_eq c1_comp c2_comp
                 else begin
                    let c1 = Env.unfold_effect_abbrev env c1 in
                    let c2 = Env.unfold_effect_abbrev env c2 in
                    if debug env <| Options.Other "Rel" then BU.print2 "solve_c for %s and %s\n" (c1.effect_name.str) (c2.effect_name.str);
                    match Env.monad_leq env c1.effect_name c2.effect_name with
                    | None ->
                       giveup env (BU.format2 "incompatible monad ordering: %s </: %s"
                                              (Print.lid_to_string c1.effect_name)
                                              (Print.lid_to_string c2.effect_name)) orig
                    | Some edge ->
                        solve_sub c1 edge c2
                 end

(* -------------------------------------------------------- *)
(* top-level interface                                      *)
(* -------------------------------------------------------- *)
let print_pending_implicits g =
    g.implicits |> List.map (fun i -> Print.term_to_string i.imp_tm) |> String.concat ", "

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
    | Trivial, [], (_, []) when not (Options.print_implicits ()) -> "{}"
    | _ ->
      let form = match g.guard_f with
          | Trivial -> "trivial"
          | NonTrivial f ->
              if debug env <| Options.Other "Rel"
              || debug env <| Options.Extreme
              || Options.print_implicits ()
              then N.term_to_string env f
              else "non-trivial" in
      let carry = List.map (fun (_, x) -> prob_to_string env x) g.deferred |> String.concat ",\n" in
      let imps = print_pending_implicits g in
      BU.format4 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
        form carry (ineqs_to_string g.univ_ineqs) imps

let new_t_problem wl env lhs rel rhs elt loc =
 let reason = if debug env <| Options.Other "ExplainRel"
              ||  Env.debug env <| Options.Other "Rel"
              then BU.format3 "Top-level:\n%s\n\t%s\n%s"
                        (N.term_to_string env lhs) (rel_to_string rel)
                        (N.term_to_string env rhs)
              else "TOP" in
 let p, wl = new_problem wl env lhs rel rhs elt loc reason in
 def_check_prob ("new_t_problem." ^ reason) (TProb p);
 TProb p, wl

let new_t_prob wl env t1 rel t2 =
 let x = S.new_bv (Some <| Env.get_range env) t1 in
 let p, wl = new_t_problem wl env t1 rel t2 (Some x) (Env.get_range env) in
 p, x, wl

let solve_and_commit env probs err =
  let tx = UF.new_transaction () in
  let sol = solve env probs in
  match sol with
    | Success (deferred, implicits) ->
      UF.commit tx;
      Some (deferred, implicits)
    | Failed (d,s) ->
      if Env.debug env <| Options.Other "ExplainRel"
      ||  Env.debug env <| Options.Other "Rel"
      then BU.print_string <| explain env d s;
      let result = err (d,s) in
      UF.rollback tx;
      result

let simplify_guard env g = match g.guard_f with
    | Trivial -> g
    | NonTrivial f ->
      if Env.debug env <| Options.Other "Simplification" then BU.print1 "Simplifying guard %s\n" (Print.term_to_string f);
      let f = N.normalize [Env.Beta; Env.Eager_unfolding; Env.Simplify; Env.Primops; Env.NoFullNorm] env f in
      if Env.debug env <| Options.Other "Simplification" then BU.print1 "Simplified guard to %s\n" (Print.term_to_string f);
      let f = match (U.unmeta f).n with
        | Tm_fvar fv when S.fv_eq_lid fv Const.true_lid -> Trivial
        | _ -> NonTrivial f in
      {g with guard_f=f}

let with_guard env prob dopt =
    match dopt with
    | None -> None
    | Some (deferred, implicits) ->
      Some <| simplify_guard env
                ({guard_f=(p_guard prob |> NonTrivial);
                  deferred=deferred;
                  univ_ineqs=([], []);
                  implicits=implicits})

let with_guard_no_simp env prob dopt = match dopt with
    | None -> None
    | Some d ->
      Some ({guard_f=(p_guard prob |> NonTrivial); deferred=d; univ_ineqs=([], []); implicits=[]})

let try_teq smt_ok env t1 t2 : option<guard_t> =
     if debug env <| Options.Other "Rel"
     then BU.print2 "try_teq of %s and %s\n" (Print.term_to_string t1) (Print.term_to_string t2);
     let prob, wl = new_t_problem (empty_worklist env) env t1 EQ t2 None (Env.get_range env) in
     let g = with_guard env prob <| solve_and_commit env (singleton wl prob smt_ok) (fun _ -> None) in
     g

let teq env t1 t2 : guard_t =
    match try_teq true env t1 t2 with
    | None ->
        FStar.Errors.log_issue
            (Env.get_range env)
            (Err.basic_type_error env None t2 t1);
        trivial_guard
    | Some g ->
        if debug env <| Options.Other "Rel"
        then BU.print3 "teq of %s and %s succeeded with guard %s\n"
                        (Print.term_to_string t1)
                        (Print.term_to_string t2)
                        (guard_to_string env g);
        g

let subtype_fail env e t1 t2 =
    Errors.log_issue (Env.get_range env) (Err.basic_type_error env (Some e) t2 t1)

let sub_comp env c1 c2 =
  let rel = if env.use_eq then EQ else SUB in
  if debug env <| Options.Other "Rel"
  then BU.print3 "sub_comp of %s --and-- %s --with-- %s\n" (Print.comp_to_string c1) (Print.comp_to_string c2) (if rel = EQ then "EQ" else "SUB");
  let prob, wl = new_problem (empty_worklist env) env c1 rel c2 None (Env.get_range env) "sub_comp" in
  let prob = CProb prob in
  def_check_prob "sub_comp" prob;
  with_guard env prob <| solve_and_commit env (singleton wl prob true)  (fun _ -> None)

let solve_universe_inequalities' tx env (variables, ineqs) =
   //variables: ?u1, ..., ?un are the universes of the inductive types we're trying to compute
   //ineqs: u1 < v1, ..., un < vn are inequality constraints gathered from checking the inductive definition
   //The basic idea is to collect all lowerbounds of each variable ?ui,
   //       excluding all of the variables themselves to avoid cycles
   //       and setting each ?ui to max(lowerbounds(?ui))
   //Then, we make a pass over all the inequalities again and check that they are all satisfied
   //This ensures, e.g., that we don't needlessly generalize types, avoid issues lik #806
   let fail u1 u2 =
        UF.rollback tx;
        raise_error (Errors.Fatal_IncompatibleUniverse, (BU.format2 "Universe %s and %s are incompatible"
                                (Print.univ_to_string u1)
                                (Print.univ_to_string u2))) (Env.get_range env)
   in
   let equiv v v' =
       match SS.compress_univ v, SS.compress_univ v' with
       | U_unif v0, U_unif v0' -> UF.univ_equiv v0 v0'
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
     | U_unif u0, U_unif v0 -> UF.univ_equiv u0 v0
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
               UF.rollback tx;
               BU.print1 "Original solved inequality constraints are: %s\n" (ineqs_to_string (variables, ineqs)));
         raise_error (Errors.Fatal_FailToSolveUniverseInEquality, ("Failed to solve universe inequalities for inductives")) (Env.get_range env))

let solve_universe_inequalities env ineqs =
    let tx = UF.new_transaction () in
    solve_universe_inequalities' tx env ineqs;
    UF.commit tx

let try_solve_deferred_constraints defer_ok env (g:guard_t) =
   let fail (d,s) =
      let msg = explain env d s in
      raise_error (Errors.Fatal_ErrorInSolveDeferredConstraints, msg) (p_loc d)
   in
   let wl = {wl_of_guard env g.deferred with defer_ok=defer_ok} in
   if Env.debug env <| Options.Other "Rel"
   then begin
         BU.print3 "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
                  (BU.string_of_bool defer_ok)
                  (wl_to_string wl)
                  (string_of_int (List.length g.implicits))
   end;
   let g =
     match solve_and_commit env wl fail with
     | Some (_::_, _) when not defer_ok ->
       failwith "Impossible: Unexpected deferred constraints remain"

     | Some (deferred, imps) ->
       {g with deferred=deferred; implicits=g.implicits@imps}

     | _ ->
       failwith "Impossible: should have raised a failure already"
   in
   solve_universe_inequalities env g.univ_ineqs;
   {g with univ_ineqs=([], [])}

let solve_deferred_constraints env (g:guard_t) =
    try_solve_deferred_constraints false env g

let solve_some_deferred_constraints env (g:guard_t) =
    try_solve_deferred_constraints true env g

let last_proof_ns : ref<option<Env.proof_namespace>> = BU.mk_ref None

let maybe_update_proof_ns env : unit =
    let pns = env.proof_ns in
    match !last_proof_ns with
    | None -> last_proof_ns := Some pns
    | Some old ->
        if old = pns
        then ()
        else (env.solver.refresh (); last_proof_ns := Some pns)

//use_smt flag says whether to use the smt solver to discharge this guard
//if use_smt = true, this function NEVER returns None, the error might come from the smt solver though
//if use_smt = false, then None means could not discharge the guard without using smt
let discharge_guard' use_env_range_msg env (g:guard_t) (use_smt:bool) : option<guard_t> =
  let debug =
       (Env.debug env <| Options.Other "Rel")
    || (Env.debug env <| Options.Other "SMTQuery")
    || (Env.debug env <| Options.Other "Tac")
  in
  let g = solve_deferred_constraints env g in
  let ret_g = {g with guard_f = Trivial} in
  if not (Env.should_verify env) then Some ret_g
  else
    match g.guard_f with
    | Trivial -> Some ret_g
    | NonTrivial vc ->
      if debug
      then Errors.diag (Env.get_range env)
                       (BU.format1 "Before normalization VC=\n%s\n" (Print.term_to_string vc));
      let vc = N.normalize [Env.Eager_unfolding; Env.Simplify; Env.Primops] env vc in
      if debug
      then Errors.diag (Env.get_range env)
                       (BU.format1 "After normalization VC=\n%s\n" (Print.term_to_string vc));
      def_check_closed_in_env (Env.get_range env) "discharge_guard'" env vc;
      match check_trivial vc with
      | Trivial -> Some ret_g
      | NonTrivial vc ->
        if not use_smt then (
            if debug then
                Errors.diag (Env.get_range env)
                            (BU.format1 "Cannot solve without SMT : %s\n" (Print.term_to_string vc));
                None
        ) else
          let _ =
            if debug
            then Errors.diag (Env.get_range env)
                             (BU.format1 "Checking VC=\n%s\n" (Print.term_to_string vc));
            let vcs =
                if Options.use_tactics()
                then begin
                    Options.with_saved_options (fun () ->
                        ignore <| Options.set_options Options.Set "--no_tactics";
                        let vcs = env.solver.preprocess env vc in
                        vcs |> List.map (fun (env, goal, opts) ->
                        env, N.normalize [Env.Simplify; Env.Primops] env goal, opts)
                    )
                end
                else [env,vc,FStar.Options.peek ()]
            in
            vcs |> List.iter (fun (env, goal, opts) ->
                    match check_trivial goal with
                    | Trivial ->
                        if debug
                        then BU.print_string "Goal completely solved by tactic\n";
                        () // do nothing

                    | NonTrivial goal ->
                        FStar.Options.push ();
                        FStar.Options.set opts;
                        maybe_update_proof_ns env;
                        if debug
                        then Errors.diag (Env.get_range env)
                                         (BU.format2 "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                 (Print.term_to_string goal)
                                                 (Env.string_of_proof_ns env));
                        if debug
                        then Errors.diag (Env.get_range env)
                                         (BU.format1 "Before calling solver VC=\n%s\n" (Print.term_to_string goal));
                        let res = env.solver.solve use_env_range_msg env goal in
                        FStar.Options.pop ();
                        res
                        )
          in
          Some ret_g

let discharge_guard_no_smt env g =
  match discharge_guard' None env g false with
  | Some g -> g
  | None  -> raise_error (Errors.Fatal_ExpectTrivialPreCondition, "Expected a trivial pre-condition") (Env.get_range env)

let discharge_guard env g =
  match discharge_guard' None env g true with
  | Some g -> g
  | None  -> failwith "Impossible, with use_smt = true, discharge_guard' should never have returned None"

let teq_nosmt (env:env) (t1:typ) (t2:typ) : option<guard_t> =
  match try_teq false env t1 t2 with
  | None -> None
  | Some g -> discharge_guard' None env g false

let resolve_implicits' env must_total forcelax g =
  let unresolved ctx_u =
    match (Unionfind.find ctx_u.ctx_uvar_head) with
    | Some _ -> false
    | None -> true
  in
  let rec until_fixpoint (acc: Env.implicits * bool) (implicits:Env.implicits) : Env.implicits =
    let out, changed = acc in
    match implicits with
    | [] -> if not changed then out else until_fixpoint ([], false) out
    | hd::tl ->
          let { imp_reason = reason; imp_tm = tm; imp_uvar = ctx_u; imp_range = r } = hd in
          if ctx_u.ctx_uvar_should_check = Allow_unresolved
          then until_fixpoint(out, true) tl
          else if unresolved ctx_u
          then begin match hd.imp_meta with
               | None ->
                    until_fixpoint (hd::out, changed) tl
               | Some (env, tau) ->
                    let t = env.synth_hook env hd.imp_uvar.ctx_uvar_typ tau in
                    // let the unifier handle setting the variable
                    let extra =
                        match teq_nosmt env t tm with
                        | None -> failwith "resolve_implicits: unifying with an unresolved uvar failed?"
                        | Some g -> g.implicits
                    in
                    let hd = { hd with imp_meta = None } in
                    until_fixpoint (out, changed) (hd :: (extra @ tl))
               end
          else if ctx_u.ctx_uvar_should_check = Allow_untyped
          then until_fixpoint(out, true) tl
          else let env = {env with gamma=ctx_u.ctx_uvar_gamma} in
               let tm = N.normalize [Env.Beta] env tm in
               let env = if forcelax then {env with lax=true} else env in
               if Env.debug env <| Options.Other "Rel"
               then BU.print5 "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                               (Print.uvar_to_string ctx_u.ctx_uvar_head)
                               (Print.term_to_string tm)
                               (Print.term_to_string ctx_u.ctx_uvar_typ)
                               reason
                               (Range.string_of_range r);
               let g =
                 try
                   env.check_type_of must_total env tm ctx_u.ctx_uvar_typ
                 with e when Errors.handleable e ->
                    Errors.add_errors [Error_BadImplicit,
                                       BU.format3 "Failed while checking implicit %s set to %s of expected type %s"
                                               (Print.uvar_to_string ctx_u.ctx_uvar_head)
                                               (N.term_to_string env tm)
                                               (N.term_to_string env ctx_u.ctx_uvar_typ), r];
                    raise e
               in
               let g = if env.is_pattern
                       then {g with guard_f=Trivial} //if we're checking a pattern sub-term, then discard its logical payload
                       else g in
               let g' =
                 match discharge_guard' (Some (fun () ->
                        BU.format4 "%s (Introduced at %s for %s resolved at %s)"
                            (Print.term_to_string tm)
                            (Range.string_of_range r)
                            reason
                            (Range.string_of_range tm.pos))) env g true with
                 | Some g -> g
                 | None   -> failwith "Impossible, with use_smt = true, discharge_guard' should never have returned None"
               in
               until_fixpoint (g'.implicits@out, true) tl in
  {g with implicits=until_fixpoint ([], false) g.implicits}

let resolve_implicits env g = resolve_implicits' env true  false g
let resolve_implicits_tac env g = resolve_implicits' env false true  g

let force_trivial_guard env g =
    let g = solve_deferred_constraints env g |> resolve_implicits env in
    match g.implicits with
        | [] -> ignore <| discharge_guard env g
        | imp::_ ->
           raise_error (Errors.Fatal_FailToResolveImplicitArgument,
                        BU.format3 "Failed to resolve implicit argument %s of type %s introduced for %s"
                                    (Print.uvar_to_string imp.imp_uvar.ctx_uvar_head)
                                    (N.term_to_string env imp.imp_uvar.ctx_uvar_typ)
                                    imp.imp_reason) imp.imp_range

let teq_nosmt_force (env:env) (t1:typ) (t2:typ) :bool =
    match teq_nosmt env t1 t2 with
    | None -> false
    | Some g ->
        force_trivial_guard env g;
        true

let universe_inequality (u1:universe) (u2:universe) : guard_t =
    //Printf.printf "Universe inequality %s <= %s\n" (Print.univ_to_string u1) (Print.univ_to_string u2);
    {trivial_guard with univ_ineqs=([], [u1,u2])}

///////////////////////////////////////////////////////////////////
let check_subtyping env t1 t2 =
    if debug env <| Options.Other "Rel"
    then BU.print2 "check_subtyping of %s and %s\n" (N.term_to_string env t1) (N.term_to_string env t2);
    let prob, x, wl = new_t_prob (empty_worklist env) env t1 SUB t2 in
    let g = with_guard env prob <| solve_and_commit env (singleton wl prob true) (fun _ -> None) in
    if debug env <| Options.Other "Rel"
    && BU.is_some g
    then BU.print3 "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                    (N.term_to_string env t1)
                    (N.term_to_string env t2)
                    (guard_to_string env (BU.must g));
    match g with
    | None -> None
    | Some g -> Some (x, g)

let get_subtyping_predicate env t1 t2 =
    match check_subtyping env t1 t2 with
    | None -> None
    | Some (x, g) ->
      Some (abstract_guard (S.mk_binder x) g)

let get_subtyping_prop env t1 t2 =
    match check_subtyping env t1 t2 with
    | None -> None
    | Some (x, g) ->
      Some (close_guard env [S.mk_binder x] g)

let subtype_nosmt env t1 t2 =
    if debug env <| Options.Other "Rel"
    then BU.print2 "try_subtype_no_smt of %s and %s\n" (N.term_to_string env t1) (N.term_to_string env t2);
    let prob, x, wl = new_t_prob (empty_worklist env) env t1 SUB t2 in
    let g = with_guard env prob <| solve_and_commit env (singleton wl prob false) (fun _ -> None) in
    match g with
    | None -> None
    | Some g ->
      let g = close_guard env [S.mk_binder x] g in
      discharge_guard' None env g false

let subtype_nosmt_force env t1 t2 =
    match subtype_nosmt env t1 t2 with
    | None -> false
    | Some g ->
        force_trivial_guard env g;
        true

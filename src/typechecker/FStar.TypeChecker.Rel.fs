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

open FStar.Common
module BU = FStar.Util //basic util
module U = FStar.Syntax.Util
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module N = FStar.TypeChecker.Normalize
module UF = FStar.Syntax.Unionfind
module Const = FStar.Parser.Const
module FC = FStar.Const
module TcComm = FStar.TypeChecker.Common

let print_ctx_uvar ctx_uvar = Print.ctx_uvar_to_string ctx_uvar

(* lazy string, for error reporting *)
type lstring = Thunk.t<string>

(* Make a thunk for a string, but keep the UF state
 * so it can be set before calling the function. This is
 * used since most error messages call term_to_string,
 * which will resolve uvars and explode if the version is
 * wrong. *)
let mklstr (f : unit -> string) =
    let uf = UF.get () in
    Thunk.mk (fun () ->
        let tx = UF.new_transaction () in
        UF.set uf;
        let r = f () in
        UF.rollback tx;
        r)

(* Instantiation of unification variables *)
type uvi =
    | TERM of ctx_uvar * term
    | UNIV of S.universe_uvar * universe

(* The set of problems currently being addressed *)
type worklist = {
    attempting:   probs;
    wl_deferred:  list<(int * lstring * prob)>; //flex-flex cases, non patterns, and subtyping constraints involving a unification variable,
    wl_deferred_to_tac: list<(int * lstring * prob)>; //problems that should be dispatched to a user-provided tactics
    ctr:          int;                          //a counter incremented each time we extend subst, used to detect if we've made progress
    defer_ok:     bool;                         //whether or not carrying constraints is ok---at the top-level, this flag is false
    smt_ok:       bool;                         //whether or not falling back to the SMT solver is permitted
    umax_heuristic_ok: bool;                    //whether or not it's ok to apply a structural match on umax us = umax us'
    tcenv:        Env.env;
    wl_implicits: implicits;                    //additional uvars introduced
    repr_subcomp_allowed:bool;                  //whether subtyping of effectful computations
                                                //with a representation (which need a monadic lift)
                                                //is allowed; disabled by default, enabled in
                                                //sub_comp which is called by the typechecker, and
                                                //will insert the appropriate lifts.
}

let as_deferred (wl_def:list<(int * lstring * prob)>) : deferred =
  List.map (fun (_, m, p) -> Thunk.force m, p) wl_def

let as_wl_deferred wl (d:deferred): list<(int * lstring * prob)> =
  List.map (fun (m, p) -> wl.ctr, Thunk.mkv m, p) d

(* --------------------------------------------------------- *)
(* <new_uvar> Generating new unification variables/patterns  *)
(* --------------------------------------------------------- *)
let new_uvar reason wl r gamma binders k should_check meta : ctx_uvar * term * worklist =
    let ctx_uvar = {
         ctx_uvar_head=UF.fresh r;
         ctx_uvar_gamma=gamma;
         ctx_uvar_binders=binders;
         ctx_uvar_typ=k;
         ctx_uvar_reason=reason;
         ctx_uvar_should_check=should_check;
         ctx_uvar_range=r;
         ctx_uvar_meta=meta;
       } in
    check_uvar_ctx_invariant reason r true gamma binders;
    let t = mk (Tm_uvar (ctx_uvar, ([], NoUseRange))) r in
    let imp = { imp_reason = reason
              ; imp_tm     = t
              ; imp_uvar   = ctx_uvar
              ; imp_range  = r
              } in
    if Env.debug wl.tcenv (Options.Other "ImplicitTrace") then
      BU.print1 "Just created uvar (Rel) {%s}\n" (Print.uvar_to_string ctx_uvar.ctx_uvar_head);
    ctx_uvar, t, {wl with wl_implicits=imp::wl.wl_implicits}

let copy_uvar u (bs:binders) t wl =
    let env = {wl.tcenv with gamma = u.ctx_uvar_gamma } in
    let env = Env.push_binders env bs in
    new_uvar ("copy:"^u.ctx_uvar_reason) wl u.ctx_uvar_range env.gamma
            (Env.all_binders env) t u.ctx_uvar_should_check u.ctx_uvar_meta

(* --------------------------------------------------------- *)
(* </new_uvar>                                               *)
(* --------------------------------------------------------- *)

(* Types used in the output of the solver *)
type solution =
  | Success of deferred * deferred * implicits
  | Failed  of prob * lstring

let extend_wl (wl:worklist) (defer_to_tac:deferred) (imps:implicits) =
  {wl with wl_deferred_to_tac=wl.wl_deferred_to_tac@(as_wl_deferred wl defer_to_tac);
           wl_implicits=wl.wl_implicits@imps}

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
      BU.format2 "UNIV %s <- %s" x (Print.univ_to_string t)

    | TERM (u, t) ->
      let x = if (Options.hide_uvar_nums()) then "?" else UF.uvar_id u.ctx_uvar_head |> string_of_int in
      BU.format2 "TERM %s <- %s" x (N.term_to_string env t)
let uvis_to_string env uvis = FStar.Common.string_of_list (uvi_to_string env) uvis
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
    wl_deferred_to_tac=[];
    ctr=0;
    tcenv=env;
    defer_ok=true;
    smt_ok=true;
    umax_heuristic_ok=true;
    wl_implicits=[];
    repr_subcomp_allowed=false;
}

let giveup env (reason : lstring) prob =
    if debug env <| Options.Other "Rel" then
        BU.print2 "Failed %s:\n%s\n" (Thunk.force reason) (prob_to_string env prob);
    Failed (prob, reason)

let giveup_lit env (reason : string) prob =
    giveup env (mklstr (fun () -> reason)) prob

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
        | ({binder_bv=bv})::bs ->
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
    def_check_closed_in (p_loc prob) msg (List.map (fun b -> b.binder_bv) <| p_scope prob) phi

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
let defer_lit reason prob wl     = defer (Thunk.mkv reason) prob wl
let attempt probs wl             =
    List.iter (def_check_prob "attempt") probs;
    {wl with attempting=probs@wl.attempting}

let mk_eq2 wl env prob t1 t2 : term * worklist =
    (* NS: Rather than introducing a new variable, it would be much preferable
            to simply compute the type of t1 here.
            Sadly, it seems to be way too expensive to call env.type_of here.
    *)
    let t_type, u = U.type_u () in
    let binders = Env.all_binders env in
    let _, tt, wl = new_uvar "eq2" wl t1.pos env.gamma binders t_type Allow_unresolved None in
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
    let gamma = List.rev (List.map (fun b -> Binding_var b.binder_bv) scope) @ (p_guard_uvar orig).ctx_uvar_gamma in
    let ctx_uvar, lg, wl =
        new_uvar ("mk_problem: logical guard for " ^ reason)
                 wl
                 Range.dummyRange
                 gamma
                 bs
                 U.ktype0
                 Allow_untyped
                 None
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
               None
  in
  let lg =
    match subject with
    | None -> lg
    | Some x -> S.mk_Tm_app lg [S.as_arg <| S.bv_to_name x] loc
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
let explain env d (s : lstring) =
    if Env.debug env <| Options.Other "ExplainRel"
    ||  Env.debug env <| Options.Other "Rel"
    then BU.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
                       (Range.string_of_range <| p_loc d)
                       (prob_to_string env d)
                       (p_reason d |> String.concat "\n\t>")
                       (Thunk.force s)
    else let d = maybe_invert_p d in
         let rel = match p_rel d with
            | EQ -> "equal to"
            | SUB -> "a subtype of"
            | _ -> failwith "impossible" in
         let lhs, rhs = match d with
            | TProb tp -> Err.print_discrepancy (N.term_to_string env) tp.lhs tp.rhs
            | CProb cp -> Err.print_discrepancy (N.comp_to_string env) cp.lhs cp.rhs in
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
      def_check_closed_in t.pos "commit" (List.map (fun b -> b.binder_bv) u.ctx_uvar_binders) t;
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
let whnf' env t    = SS.compress (N.normalize [Env.Beta; Env.Reify; Env.Weak; Env.HNF] env (U.unmeta t)) |> U.unlazy_emb
let sn' env t       = SS.compress (N.normalize [Env.Beta; Env.Reify] env t) |> U.unlazy_emb
let sn env t =
  Profiling.profile
    (fun () ->
      sn' env t)
    (Some (Ident.string_of_lid (Env.current_module env)))
    "FStar.TypeChecker.Rel.sn"
let norm_with_steps profiling_tag steps env t =
  Profiling.profile
    (fun () ->
      N.normalize steps env t)
    (Some (Ident.string_of_lid (Env.current_module env)))
    profiling_tag


let should_strongly_reduce t =
    let h, _ = U.head_and_args t in
    match (SS.compress h).n with
    | Tm_constant FStar.Const.Const_reify -> true
    | _ -> false

let whnf env t =
  Profiling.profile
    (fun () ->
      if should_strongly_reduce t
      then SS.compress (N.normalize [Env.Beta; Env.Reify; Env.Exclude Env.Zeta; Env.UnfoldUntil delta_constant] env t) |> U.unlazy_emb
      else whnf' env t)
    (Some (Ident.string_of_lid (Env.current_module env)))
    "FStar.TypeChecker.Rel.whnf"

let norm_arg env t = sn env (fst t), snd t
let sn_binders env (binders:binders) =
    binders |> List.map (fun b -> {b with binder_bv={b.binder_bv with sort=sn env b.binder_bv.sort} })

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

let normalize_refinement steps env t0 : term =
  Profiling.profile
    (fun () -> N.normalize_refinement steps env t0)
    (Some (Ident.string_of_lid (Env.current_module env)))
    "FStar.TypeChecker.Rel.normalize_refinement"

let base_and_refinement_maybe_delta should_delta env t1 =
   let norm_refinement env t =
       let steps =
         if should_delta
         then [Env.Weak; Env.HNF; Env.UnfoldUntil delta_constant]
         else [Env.Weak; Env.HNF] in
       normalize_refinement steps env t
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
    mk (Tm_refine(y, phi)) t_base.pos

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

(* A flexible term: the full term,
 * its unification variable at the head,
 * and the arguments the uvar is applied to. *)
type flex_t =
  | Flex of (term * ctx_uvar * args)

let flex_reason (Flex (_, u, _)) = u.ctx_uvar_reason

let flex_t_to_string (Flex (_, c, args)) =
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

(* ensure_no_uvar_subst: Make sure the uvar at the head of t0 is not
 * affected by a the substitution in the Tm_uvar node.
 *
 * In the case that it is, first solve it to a new appropriate uvar
 * without a substitution. This function returns t again, though it is
 * unchanged (the changes only happen in the UF graph).
 *
 * The way we generate the new uvar is by making a new variable with
 * that is "hoisted" and which we apply to the binders of the original
 * uvar. There is an optimization in place to hoist as few binders as
 * possible.
 *
 * Example: If we have ((x:a),(y:b),(z:c) |- ?u : ty)[y <- 42], we will
 * make ?u' with x in its binders, abstracted over y and z:
 *
 * (x |- ?u') : b -> c -> ty
 *
 * (we keep x since it's unaffected by the substitution; z is not since
 * it has y in scope) and then solve
 *
 * ?u <- (?u' y z)
 *
 * Which means the original term now compresses to ?u' 42 z. The flex
 * problem we now return is
 *
 * ?u', [42 z]
 *
 * We also return early if the substitution is empty or if the uvar is
 * totally unaffected by it.
 *)
let ensure_no_uvar_subst (t0:term) (wl:worklist)
  : term * worklist
  = (* Returns true iff the variable x is not affected by substitution s *)
    let bv_not_affected_by (s:subst_ts) (x:bv) : bool =
      let t_x = S.bv_to_name x in
      let t_x' = SS.subst' s t_x in
      match (SS.compress t_x').n with
      | Tm_name y ->
         S.bv_eq x y // Check if substituting returned the same variable
      | _ -> false
    in
    let binding_not_affected_by (s:subst_ts) (b:binding) : bool =
      match b with
      | Binding_var x -> bv_not_affected_by s x
      | _ -> true
    in
    let head, args = U.head_and_args t0 in
    match (SS.compress head).n with
    | Tm_uvar (uv, ([], _)) ->
      (* No subst, nothing to do *)
      t0, wl

    | Tm_uvar (uv, _) when List.isEmpty uv.ctx_uvar_binders ->
      (* No binders in scope, also good *)
      t0, wl

    | Tm_uvar (uv, s) ->
      (* Obtain the maximum prefix of the binders that can remain as-is
       * (gamma is a snoc list, so we want a suffix of it. *)
      let gamma_aff, new_gamma = FStar.Common.max_suffix (binding_not_affected_by s)
                                                         uv.ctx_uvar_gamma
      in
      begin match gamma_aff with
      | [] ->
        (* Not affected by the substitution at all, do nothing *)
        t0, wl
      | _ ->
        (* At least one variable is affected, make a new uvar *)
        let dom_binders = Env.binders_of_bindings gamma_aff in
        let v, t_v, wl = new_uvar (uv.ctx_uvar_reason ^ "; force delayed")
                         wl
                         t0.pos
                         new_gamma
                         (Env.binders_of_bindings new_gamma)
                         (U.arrow dom_binders (S.mk_Total uv.ctx_uvar_typ))
                         uv.ctx_uvar_should_check
                         uv.ctx_uvar_meta
        in

        (* Solve the old variable *)
        let args_sol = List.map (fun ({binder_bv=x;binder_qual=i}) -> S.bv_to_name x, i) dom_binders in
        let sol = S.mk_Tm_app t_v args_sol t0.pos in
        U.set_uvar uv.ctx_uvar_head sol;

        (* Make a term for the new uvar, applied to the substitutions of
         * the abstracted arguments, plus all the original arguments. *)
        let args_sol_s = List.map (fun (a, i) -> SS.subst' s a, i) args_sol in
        let t = S.mk_Tm_app t_v (args_sol_s @ args) t0.pos in
        t, wl
      end
    | _ ->
      failwith (BU.format3 "ensure_no_uvar_subst: expected a uvar at the head (%s-%s-%s)"
                           (Print.tag_of_term t0)
                           (Print.tag_of_term head)
                           (Print.tag_of_term (SS.compress head)))

(* Only call if ensure_no_uvar_subst was called on t before *)
let destruct_flex_t' t : flex_t =
    let head, args = U.head_and_args t in
    match (SS.compress head).n with
    | Tm_uvar (uv, s) ->
      Flex (t, uv, args)
    | _ -> failwith "Not a flex-uvar"

(* Destruct a term into its uvar head and arguments *)
let destruct_flex_t t wl : flex_t * worklist =
  let t, wl = ensure_no_uvar_subst t wl in
  (* If there's any substitution on the head of t, it must
   * have been made trivial by the call above, so
   * calling destruct_flex_t' is fine. *)
  destruct_flex_t' t, wl

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
                            (List.map (fun b -> b.binder_bv) <| p_scope prob) phi;
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
            | Tm_name x -> [{binder_bv=x;binder_qual=i;binder_attrs=[]}]
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
        else let (Flex (_, uv, args), wl)  = destruct_flex_t g wl in
             assign_solution (args_as_binders args) uv phi;
             wl
    in
    commit uvis;
    {wl with ctr=wl.ctr + 1}

let extend_solution pid sol wl =
    if Env.debug wl.tcenv <| Options.Other "Rel"
    then BU.print2 "Solving %s: with [%s]\n" (string_of_int pid)
                                             (uvis_to_string wl.tcenv sol);
    commit sol;
    {wl with ctr=wl.ctr+1}

let solve_prob (prob : prob) (logical_guard : option<term>) (uvis : list<uvi>) (wl:worklist) : worklist =
    def_check_prob "solve_prob.prob" prob;
    BU.iter_opt logical_guard (def_check_scoped "solve_prob.guard" prob);
    if Env.debug wl.tcenv <| Options.Other "Rel"
    then BU.print2 "Solving %s: with %s\n" (string_of_int <| p_pid prob)
                                           (uvis_to_string wl.tcenv uvis);
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
  | binder1::bs_tail,
    ({binder_bv=b';binder_qual=i'})::bs'_tail ->
    if S.bv_eq binder1.binder_bv b'
    then let pfx, rest = maximal_prefix bs_tail bs'_tail in
         binder1::pfx, rest
    else [], (bs, bs')
  | _ -> [], (bs, bs')

let extend_gamma (g:gamma) (bs:binders) =
    List.fold_left (fun g ({binder_bv=x}) -> Binding_var x::g) g bs

let gamma_until (g:gamma) (bs:binders) =
    match List.last bs with
    | None -> []
    | Some ({binder_bv=x}) ->
      match BU.prefix_until (function Binding_var x' -> S.bv_eq x x' | _  -> false) g with
      | None -> []
      | Some (_, bx, rest) -> bx::rest

(*
 * AR: 07/20: generalizing restrict
 *
 * Given G_s |- ?u_s bs : t_s and G_t |- ?u_t : t_t, this code restricts G_t to the
 *   maximal prefix of G_s and G_t, creating a new uvar maximal_prefix(G_s, G_t) |- ?u : t_t,
 *   and assigning ?u_t = ?u
 *
 * However simply doing this does not allow the solution of ?u to mention the binders bs
 *
 * Instead, we filter bs that also appear in G_t but not in the maximal prefix and
 *   allow the solution of G_t to contain them
 *
 * (The solution of ?u_t is already allowed to contain the ones appearing in the maximal prefix)
 *
 * So the new uvar that's created is maximal_prefix(G_s, G_t) |- ?u : bs -> t_t
 *   and assigning ?u_t = ?u bs
 *
 * This comes in handy for the flex-rigid case, where the arguments of the flex are a pattern
 *)
let restrict_ctx env (tgt:ctx_uvar) (bs:binders) (src:ctx_uvar) wl : worklist =
  let pfx, _ = maximal_prefix tgt.ctx_uvar_binders src.ctx_uvar_binders in
  let g = gamma_until src.ctx_uvar_gamma pfx in

  //t is the type at which new uvar ?u should be created
  //f is a function that applied to the new uvar term should return the term that ?u_t should be solved to
  let aux (t:typ) (f:term -> term) =
    let _, src', wl = new_uvar ("restricted " ^ (Print.uvar_to_string src.ctx_uvar_head)) wl
      src.ctx_uvar_range g pfx t
      src.ctx_uvar_should_check src.ctx_uvar_meta in
    U.set_uvar src.ctx_uvar_head (f src');
    wl in

  let bs = bs |> List.filter (fun ({binder_bv=bv1}) ->
    src.ctx_uvar_binders |> List.existsb (fun ({binder_bv=bv2}) -> S.bv_eq bv1 bv2) &&  //binder exists in G_t
    not (pfx |> List.existsb (fun ({binder_bv=bv2}) -> S.bv_eq bv1 bv2))) in  //but not in the maximal prefix
    
  if List.length bs = 0 then aux src.ctx_uvar_typ (fun src' -> src')  //no abstraction over bs
  else begin
    aux
      (src.ctx_uvar_typ |> env.universe_of env |> Some |> S.mk_Total' src.ctx_uvar_typ |> U.arrow bs)  //bs -> Tot t_t
      (fun src' -> S.mk_Tm_app  //?u bs
        src'
        (bs |> S.binders_to_names |> List.map S.as_arg)
        src.ctx_uvar_range)
  end

let restrict_all_uvars env (tgt:ctx_uvar) (bs:binders) (sources:list<ctx_uvar>) wl : worklist =
    List.fold_right (restrict_ctx env tgt bs) sources wl

let intersect_binders (g:gamma) (v1:binders) (v2:binders) : binders =
    let as_set v =
        v |> List.fold_left (fun out x -> BU.set_add x.binder_bv out) S.no_names in
    let v1_set = as_set v1 in
    let ctx_binders =
        List.fold_left (fun out b -> match b with Binding_var x -> BU.set_add x out | _ -> out)
                        S.no_names
                        g
    in
    let isect, _ =
        v2 |> List.fold_left (fun (isect, isect_set) b ->
            let x, imp = b.binder_bv, b.binder_qual in
            if not <| BU.set_mem x v1_set
            then //definitely not in the intersection
                 isect, isect_set
            else //maybe in the intersect, if its type is only dependent on prior elements in the telescope
                 let fvs = Free.names x.sort in
                 if BU.set_is_subset_of fvs isect_set
                 then b::isect, BU.set_add x isect_set
                 else isect, isect_set)
        ([], ctx_binders) in
    List.rev isect

let binders_eq v1 v2 =
  List.length v1 = List.length v2
  && List.forall2 (fun ({binder_bv=a}) ({binder_bv=b}) -> S.bv_eq a b) v1 v2

let name_exists_in_binders x bs =
    BU.for_some (fun ({binder_bv=y}) -> S.bv_eq x y) bs

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
          else aux (({binder_bv=a;binder_qual=i;binder_attrs=[]})::seen) args
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
      if string_of_lid env.curmodule = nsstr fv.fv_name.v && not env.is_iface  //AR: TODO: this is to prevent unfolding of abstract symbols in the extracted interface
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

    | Tm_constant FC.Const_reify, Tm_constant FC.Const_reify -> FullMatch
    | Tm_constant FC.Const_reify, _
    | _, Tm_constant FC.Const_reify -> HeadMatch true
    | Tm_constant c, Tm_constant d -> if FC.eq_const c d then FullMatch else MisMatch(None, None)

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
    | Tm_match _, Tm_match _
    | Tm_abs _, Tm_abs _ -> HeadMatch true

    | _ -> MisMatch(delta_depth_of_term env t1, delta_depth_of_term env t2)

(* Does t1 head-match t2, after some delta steps? *)
let head_matches_delta env wl t1 t2 : (match_result * option<(typ*typ)>) =
    let maybe_inline t =
        let head = U.head_of (unrefine env t) in
        if Env.debug env <| Options.Other "RelDelta" then
            BU.print2 "Head of %s is %s\n" (Print.term_to_string t) (Print.term_to_string head);
        match (U.un_uinst head).n with
        | Tm_fvar fv ->
          begin
          match Env.lookup_definition
                    [Env.Unfold delta_constant;
                     Env.Eager_unfolding_only]
                    env
                    fv.fv_name.v
          with
          | None ->
            if Env.debug env <| Options.Other "RelDelta" then
                BU.print1 "No definition found for %s\n" (Print.term_to_string head);
            None
          | Some _ ->
            let basic_steps =
                [Env.UnfoldUntil delta_constant;
                 Env.Weak;
                 Env.HNF;
                 Env.Primops;
                 Env.Beta;
                 Env.Eager_unfolding;
                 Env.Iota]
            in
            let steps =
              if wl.smt_ok then basic_steps
              else Env.Exclude Env.Zeta::basic_steps
                   //NS: added this to prevent unifier looping
                   //see bug606.fst
                   //should we always disable Zeta here?
            in
            let t' = norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.1" steps env t in
            if U.eq_tm t t' = U.Equal //if we didn't inline anything
            then None
            else let _ = if Env.debug env <| Options.Other "RelDelta"
                         then BU.print2 "Inlined %s to %s\n"
                                        (Print.term_to_string t)
                                        (Print.term_to_string t') in
                 Some t'
          end
        | _ -> None
    in
    let success d r t1 t2 = (r, (if d>0 then Some(t1, t2) else None)) in
    let fail d r t1 t2 = (r, (if d>0 then Some(t1, t2) else None)) in

    (*
     * AR: When we delta-unfold the terms below, it may happen that application of an fv with
     *       delta depth say 1 doesn't unfold because it is marked with strict_on_arguments
     *     To prevent looping in that case, we make sure that we have made progress
     *       in an unfolding call to the normalizer
     *     This made_progress function is checking that we have made progress in unfolding t to t'
     *     See #2184
     *)
    let made_progress t t' =
      let head, head' = U.head_and_args t |> fst, U.head_and_args t' |> fst in
      not (U.eq_tm head head' = U.Equal) in

    let rec aux retry n_delta t1 t2 =
        let r = head_matches env t1 t2 in
        if Env.debug env <| Options.Other "RelDelta" then
            BU.print3 "head_matches (%s, %s) = %s\n"
                (Print.term_to_string t1)
                (Print.term_to_string t2)
                (string_of_match_result r);
        let reduce_one_and_try_again (d1:delta_depth) (d2:delta_depth) =
          let d1_greater_than_d2 = Common.delta_depth_greater_than d1 d2 in
          let t1, t2, made_progress =
            if d1_greater_than_d2
            then let t1' = normalize_refinement [Env.UnfoldUntil d2; Env.Weak; Env.HNF] env t1 in
                 t1', t2, made_progress t1 t1'
            else let t2' = normalize_refinement [Env.UnfoldUntil d1; Env.Weak; Env.HNF] env t2 in
                 t1, t2', made_progress t2 t2' in
          if made_progress
          then aux retry (n_delta + 1) t1 t2
          else fail n_delta r t1 t2
        in

        let reduce_both_and_try_again (d:delta_depth) (r:match_result) =
          match Common.decr_delta_depth d with
          | None -> fail n_delta r t1 t2
          | Some d ->
            let t1' = normalize_refinement [Env.UnfoldUntil d; Env.Weak; Env.HNF] env t1 in
            let t2' = normalize_refinement [Env.UnfoldUntil d; Env.Weak; Env.HNF] env t2 in
            if made_progress t1 t1' &&
               made_progress t2 t2'
            then aux retry (n_delta + 1) t1' t2'
            else fail n_delta r t1 t2
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
          u.ctx_uvar_binders |> BU.for_some (fun ({binder_bv=y}) ->
          bs |> BU.for_some (fun ({binder_bv=x}) -> S.bv_eq x y))
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
  | UFailed   of lstring

let ufailed_simple (s:string) : univ_eq_sol =
  UFailed (Thunk.mkv s)

let ufailed_thunk (s: unit -> string) : univ_eq_sol =
  UFailed (mklstr s)

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
      let common_elts = u1 |> List.fold_left (fun uvs uv1 -> if u2 |> List.existsML (fun uv2 -> U.eq_univs uv1 uv2) then uv1::uvs else uvs) [] in
      let filter = List.filter (fun u -> not (common_elts |> List.existsML (fun u' -> U.eq_univs u u'))) in
      filter u1, filter u2
    in

    let try_umax_components u1 u2 msg =
        if not wl.umax_heuristic_ok
        then ufailed_simple "Unable to unify universe terms with umax"
        else
        match u1, u2 with
            | U_max us1, U_max us2 ->
              begin
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
              else ufailed_thunk
                             (fun () -> BU.format2 "Unable to unify universes: %s and %s"
                                                   (Print.univ_to_string u1)
                                                   (Print.univ_to_string u2))
              end
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

            | _ ->
              ufailed_thunk (fun () ->
                            BU.format3 "Unable to unify universes: %s and %s (%s)"
                                       (Print.univ_to_string u1)
                                       (Print.univ_to_string u2) msg) in

    match u1, u2 with
        | U_bvar _, _
        | U_unknown, _
        | _, U_bvar _
        | _, U_unknown -> failwith (BU.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                                        (Print.univ_to_string u1)
                                        (Print.univ_to_string u2))

        | U_name x, U_name y ->
          if (string_of_id x) = (string_of_id y)
          then USolved wl
          else ufailed_simple "Incompatible universes"

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
          ufailed_simple "Incompatible universes"

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
    | EQ     -> mk_eq2 wl env (TProb problem) t1 t2
    | SUB    -> has_type_guard t1 t2, wl
    | SUBINV -> has_type_guard t2 t1, wl

let is_flex_pat = function
    | Flex (_, _, []) -> true
    | _ -> false

(** If the head uvar of the flex term is tagged with a `Ctx_uvar_meta_attr a`
    and if a term tagged with attribute `a` is in scope,
    then this problem should be deferred to a tactic *)
let should_defer_flex_to_user_tac env (wl:worklist) (f:flex_t) =
  let (Flex (_, u, _)) = f in
  let b = DeferredImplicits.should_defer_uvar_to_user_tac wl.tcenv u in

  if Env.debug env <| Options.Other "ResolveImplicitsHook"
  then BU.print2 "Rel.should_defer_flex_to_user_tac for %s returning %s\n"
         (Print.ctx_uvar_to_string_no_reason u) (string_of_bool b);

  b

(* <quasi_pattern>:
        Given a term (?u_(bs;t) e1..en)
        returns None in case the arity of the type t is less than n
        otherwise returns Some (x1 ... xn)
        where if ei is a variable distinct from bs and all the ej
            then xi = ei
            else xi is a fresh variable
    *)
let quasi_pattern env (f:flex_t) : option<(binders * typ)> =
    let (Flex (_, {ctx_uvar_binders=ctx; ctx_uvar_typ=t_hd}, args)) = f in
    let name_exists_in x bs =
        BU.for_some (fun ({binder_bv=y}) -> S.bv_eq x y) bs
    in
    let rec aux pat_binders formals t_res args =
        match formals, args with
        | [], []
        |  _, [] ->
          Some (List.rev pat_binders, U.arrow formals (S.mk_Total t_res))

        | fml::formals, (a, a_imp)::args ->
            begin
            let formal, formal_imp = fml.binder_bv, fml.binder_qual in
            match (SS.compress a).n with
            | Tm_name x ->
                if name_exists_in x ctx
                ||  name_exists_in x pat_binders
                then //we already have x
                     //so don't include it in the quasi-pattern
                     aux (fml :: pat_binders) formals t_res args
                else let x = {x with sort=formal.sort} in
                        let subst = [NT(formal, S.bv_to_name x)] in
                        let formals = SS.subst_binders subst formals in
                        let t_res = SS.subst subst t_res in
                        aux (({binder_bv={x with sort=formal.sort};binder_qual=a_imp;binder_attrs=fml.binder_attrs}) :: pat_binders) formals t_res args
            | _ -> //it's not a name, so it can't be included in the patterns
            aux (fml :: pat_binders) formals t_res args
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
    if Env.debug env <| Options.Other "ImplicitTrace" then
      BU.print1 "solve: wl_implicits = %s\n"
                    (Common.implicits_to_string probs.wl_implicits);

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
        then solve_t env tp probs
        else if probs.defer_ok
        then maybe_defer_to_user_tac env tp "deferring flex_rigid or flex_flex subtyping" probs
        else if rank=Flex_flex
        then solve_t env ({tp with relation=EQ}) probs //turn flex_flex subtyping into flex_flex eq
        else solve_rigid_flex_or_flex_rigid_subtyping rank env tp probs
      end

    | None ->
         begin
         match probs.wl_deferred with
         | [] ->
           Success ([], as_deferred probs.wl_deferred_to_tac, probs.wl_implicits) //Yay ... done!

         | _ ->
           let attempt, rest = probs.wl_deferred |> List.partition (fun (c, _, _) -> c < probs.ctr) in
           match attempt with
            | [] -> //can't solve yet; defer the rest
              Success(as_deferred probs.wl_deferred,
                      as_deferred probs.wl_deferred_to_tac,
                      probs.wl_implicits)

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
      solve env (defer_lit "" orig wl)

and solve_maybe_uinsts (env:Env.env) (orig:prob) (t1:term) (t2:term) (wl:worklist) : univ_eq_sol =
    let rec aux wl us1 us2 = match us1, us2 with
        | [], [] -> USolved wl

        | u1::us1, u2::us2 ->
          begin match solve_universe_eq (p_pid orig) wl u1 u2 with
            | USolved wl ->
              aux wl us1 us2

            | failed_or_deferred -> failed_or_deferred
          end

        | _ -> ufailed_simple "Unequal number of universes" in

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

and giveup_or_defer (env:Env.env) (orig:prob) (wl:worklist) (msg:lstring) : solution =
    if wl.defer_ok
    then begin
        if Env.debug env <| Options.Other "Rel" then
            BU.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" (prob_to_string env orig) (Thunk.force msg);
        solve env (defer msg orig wl)
    end
    else giveup env msg orig

and defer_to_user_tac (env:Env.env) (orig:prob) reason (wl:worklist) : solution =
  if Env.debug env <| Options.Other "Rel" then
    BU.print1 "\n\t\tDeferring %s to a tactic\n" (prob_to_string env orig);
  let wl = solve_prob orig None [] wl in
  let wl = {wl with wl_deferred_to_tac=(wl.ctr, Thunk.mkv reason, orig)::wl.wl_deferred_to_tac} in
  solve env wl

and maybe_defer_to_user_tac (env:Env.env) prob reason wl : solution =
  match prob.relation with
  | EQ ->
    let should_defer_tac t =
      let head, _ = U.head_and_args t in
      match (SS.compress head).n with
      | Tm_uvar(uv, _) ->
        DeferredImplicits.should_defer_uvar_to_user_tac wl.tcenv uv, uv.ctx_uvar_reason
      | _ -> false, ""
    in
    let l1, r1 = should_defer_tac prob.lhs in
    let l2, r2 = should_defer_tac prob.rhs in
    if l1 || l2
    then defer_to_user_tac env (TProb prob) (r1 ^ ", " ^ r2) wl
    else solve env (defer_lit reason (TProb prob) wl)
  | _ -> solve env (defer_lit reason (TProb prob) wl)

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
            let mr, ts = head_matches_delta env wl t1 t2 in
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
                  | Success (_, defer_to_tac, imps) ->
                    UF.commit tx;
                    Some (extend_wl wl defer_to_tac imps)

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
             | None -> giveup_lit env "flex-arrow subtyping, not a quasi pattern" (TProb tp)
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
      match solve_t env eq_prob ({wl' with defer_ok=false; wl_implicits = []; attempting=sub_probs}) with
      | Success (_, defer_to_tac, imps) ->
         let wl = {wl' with attempting=rest} in
         let wl = extend_wl wl defer_to_tac imps in
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
            giveup env (Thunk.map (fun s -> "failed to solve the sub-problems: " ^ s) msg) p)
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
        let bs_lhs_args = List.map (fun ({binder_bv=x;binder_qual=i}) -> S.bv_to_name x, i) bs_lhs in
        let (Flex (_, u_lhs, _)) = lhs in
        let imitate_comp bs bs_terms c wl =
           let imitate_tot_or_gtot t uopt f wl =
              let k, univ =
                  match uopt with
                  | None ->
                    U.type_u()
                  | Some univ ->
                    S.mk (Tm_type univ) t.pos, univ
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
             (* Drop the decreases flag, it is not needed and
              * wouldn't be properly scoped either. *)
             let nodec flags = List.filter (function DECREASES _ -> false
                                                     | _ -> true) flags in
             let ct' = {ct with result_typ=fst (List.hd out_args);
                                effect_args=List.tl out_args;
                                flags=nodec ct.flags} in
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

            | ({binder_bv=x;binder_qual=imp;binder_attrs=attrs})::formals ->
              let _ctx_u_x, u_x, wl = copy_uvar u_lhs (bs_lhs@bs) (U.type_u() |> fst) wl in
              //printfn "Generated formal %s where %s" (Print.term_to_string t_y) (Print.ctx_uvar_to_string ctx_u_x);
              let y = S.new_bv (Some (S.range_of_bv x)) u_x in
              aux (bs@[{binder_bv=y;binder_qual=imp;binder_attrs=attrs}]) (bs_terms@[S.bv_to_name y, imp]) formals wl
         in
         let _, occurs_ok, msg = occurs_check u_lhs arrow in
         if not occurs_ok
         then giveup_or_defer env orig wl (mklstr (fun () -> "occurs-check failed: " ^ (Option.get msg)))
         else aux [] [] formals wl

and solve_binders (env:Env.env) (bs1:binders) (bs2:binders) (orig:prob) (wl:worklist)
                  (rhs:worklist -> binders -> Env.env -> list<subst_elt> -> (prob * worklist)) : solution =

   if debug env <| Options.Other "Rel"
   then BU.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                       (Print.binders_to_string ", " bs1)
                       (rel_to_string (p_rel orig))
                       (Print.binders_to_string ", " bs2);

   (*
    * AR: adding env to the return type
    *
    *     `aux` solves the binders problems xs REL ys, and keeps on adding the binders to env
    *       so that subsequent binders are solved in the right env
    *     when all the binders are solved, it creates the rhs problem and returns it
    *     the problem was that this rhs problem was getting solved in the original env,
    *       since `aux` never returned the env with all the binders
    *     so far it was fine, but with layered effects, we have to be really careful about the env
    *     so now we return the updated env, and the rhs is solved in that final env
    *     (see how `aux` is called after its definition below)
    *)
   let rec aux wl scope env subst (xs:binders) (ys:binders) : Env.env * either<(probs * formula), string> * worklist =
        match xs, ys with
        | [], [] ->
          let rhs_prob, wl = rhs wl scope env subst in
          if debug env <| Options.Other "Rel"
          then BU.print1 "rhs_prob = %s\n" (prob_to_string env rhs_prob);
          let formula = p_guard rhs_prob in
          env, Inl ([rhs_prob], formula), wl

        | x::xs, y::ys when (U.eq_aqual x.binder_qual y.binder_qual = U.Equal) ->
           let hd1, imp = x.binder_bv, x.binder_qual in
           let hd2, imp' = y.binder_bv, y.binder_qual in
           let hd1 = {hd1 with sort=Subst.subst subst hd1.sort} in //open both binders
           let hd2 = {hd2 with sort=Subst.subst subst hd2.sort} in
           let prob, wl = mk_t_problem wl scope orig hd1.sort (invert_rel <| p_rel orig) hd2.sort None "Formal parameter" in
           let hd1 = freshen_bv hd1 in
           let subst = DB(0, hd1)::SS.shift_subst 1 subst in  //extend the substitution
           let env = Env.push_bv env hd1 in
           begin
           match aux wl (scope @ [{x with binder_bv=hd1}]) env subst xs ys with
           | env, Inl (sub_probs, phi), wl ->
             let phi =
                 U.mk_conj (p_guard prob)
                           (close_forall env [{x with binder_bv=hd1}] phi) in
             if debug env <| Options.Other "Rel"
             then BU.print2 "Formula is %s\n\thd1=%s\n" (Print.term_to_string phi) (Print.bv_to_string hd1);
             env, Inl (prob::sub_probs, phi), wl

           | fail -> fail
           end

        | _ -> env, Inr "arity or argument-qualifier mismatch", wl in

   match aux wl [] env [] bs1 bs2 with
   | env, Inr msg, wl -> giveup_lit env msg orig
   | env, Inl (sub_probs, phi), wl ->
     let wl = solve_prob orig (Some phi) [] wl in
     solve env (attempt sub_probs wl)

and try_solve_without_smt_or_else
        (env:Env.env) (wl:worklist)
        (try_solve: (Env.env -> worklist -> solution))
        (else_solve: Env.env -> worklist -> (prob * lstring) -> solution)
    : solution =
    let wl' = {wl with defer_ok=false;
                       smt_ok=false;
                       umax_heuristic_ok=false;
                       attempting=[];
                       wl_deferred=[];
                       wl_implicits=[]} in
    let tx = UF.new_transaction () in
    match try_solve env wl' with
    | Success (_, defer_to_tac, imps) ->
      UF.commit tx;
      let wl = extend_wl wl defer_to_tac imps in
      solve env wl
    | Failed (p, s) ->
      UF.rollback tx;
      else_solve env wl (p,s)

and solve_t (env:Env.env) (problem:tprob) (wl:worklist) : solution =
    def_check_prob "solve_t" (TProb problem);
    solve_t' env (compress_tprob wl.tcenv problem) wl

and solve_t_flex_rigid_eq env (orig:prob) wl
                              (lhs:flex_t)
                              (rhs:term)
    : solution =
    if Env.debug env <| Options.Other "Rel" then
      BU.print_string "solve_t_flex_rigid_eq\n";

    if should_defer_flex_to_user_tac env wl lhs
    then defer_to_user_tac env orig (flex_reason lhs) wl
    else

    let binders_as_bv_set (bs:binders) =
        FStar.Util.as_set (List.map (fun b -> b.binder_bv) bs)
                          Syntax.order_bv
    in

    let mk_solution env (lhs:flex_t) (bs:binders) (rhs:term) =
        let (Flex (_, ctx_u, _)) = lhs in
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
        if Env.debug env <| Options.Other "Rel" then
          BU.print_string "try_quasi_pattern\n";
        match quasi_pattern env lhs with
        | None ->
          Inl "Not a quasi-pattern", wl

        | Some (bs, _) ->
          let (Flex (t_lhs, ctx_u, args)) = lhs in
          let uvars, occurs_ok, msg = occurs_check ctx_u rhs in
          if not occurs_ok
          then Inl ("quasi-pattern, occurs-check failed: " ^ (Option.get msg)), wl
          else let fvs_lhs = binders_as_bv_set (ctx_u.ctx_uvar_binders@bs) in
               let fvs_rhs = Free.names rhs in
               if not (BU.set_is_subset_of fvs_rhs fvs_lhs)
               then Inl ("quasi-pattern, free names on the RHS are not included in the LHS"), wl
               else Inr (mk_solution env lhs bs rhs), restrict_all_uvars env ctx_u [] uvars wl
    in

    let imitate_app (orig:prob) (env:Env.env) (wl:worklist)
                    (lhs:flex_t) (bs_lhs:binders) (t_res_lhs:term)
                    (rhs:term)
        : solution =
        //if Env.debug env <| Options.Other "Rel"
        //then BU.print4 "imitate_app 1:\n\tlhs=%s\n\tbs_lhs=%s\n\tt_res_lhs=%s\n\trhs=%s\n"
        //    (flex_t_to_string lhs)
        //    (Print.binders_to_string ", " bs_lhs)
        //    (Print.term_to_string t_res_lhs)
        //    (Print.term_to_string rhs);
        let rhs_hd, args = U.head_and_args rhs in
        let args_rhs, last_arg_rhs = BU.prefix args in
        let rhs' = S.mk_Tm_app rhs_hd args_rhs rhs.pos in
        //if Env.debug env <| Options.Other "Rel"
        //then BU.print2 "imitate_app 2:\n\trhs'=%s\n\tlast_arg_rhs=%s\n"
        //            (Print.term_to_string rhs')
        //            (Print.args_to_string [last_arg_rhs]);
        let (Flex (t_lhs, u_lhs, _lhs_args)) = lhs in
        let lhs', lhs'_last_arg, wl =
              let t_last_arg = env.type_of_well_typed ({env with lax=true; use_bv_sorts=true; expected_typ=None}) (fst last_arg_rhs) in
              //FIXME: this may be an implicit arg ... fix qualifier
              //AR: 07/20: note the type of lhs' is t_last_arg -> t_res_lhs
              let _, lhs', wl =
                let b = S.null_binder t_last_arg in
                copy_uvar u_lhs (bs_lhs@[b])
                (t_res_lhs |> env.universe_of env |> Some |> S.mk_Total' t_res_lhs |> U.arrow [b]) wl in
              let _, lhs'_last_arg, wl = copy_uvar u_lhs bs_lhs t_last_arg wl in
              lhs', lhs'_last_arg, wl
        in
        //if Env.debug env <| Options.Other "Rel"
        //then BU.print2 "imitate_app 3:\n\tlhs'=%s\n\tlast_arg_lhs=%s\n"
        //            (Print.term_to_string lhs')
        //            (Print.term_to_string lhs'_last_arg);
        let sol = [TERM(u_lhs, U.abs bs_lhs (S.mk_Tm_app lhs' [S.as_arg lhs'_last_arg] t_lhs.pos)
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
        if Env.debug env <| Options.Other "Rel" then
          BU.print_string "first_order\n";
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
           let msg = mklstr (fun () ->
                        BU.format1 "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                          (prob_to_string env orig)) in
           giveup_or_defer env orig wl msg

        | Some (bs_lhs, t_res_lhs) ->
          if is_app rhs
          then imitate_app orig env wl lhs bs_lhs t_res_lhs rhs
          else if is_arrow rhs
          then imitate_arrow orig env wl lhs bs_lhs t_res_lhs EQ rhs
          else
            let msg = mklstr (fun () ->
                                  BU.format1 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                  (prob_to_string env orig)) in
            giveup_or_defer env orig wl msg
    in

    match p_rel orig with
    | SUB
    | SUBINV ->
      if wl.defer_ok
      then giveup_or_defer env orig wl (Thunk.mkv "flex-rigid subtyping")
      else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs

    | EQ ->
      let (Flex (_t1, ctx_uv, args_lhs)) = lhs in
      match pat_vars env ctx_uv.ctx_uvar_binders args_lhs with
      | Some lhs_binders -> //Pattern
        if Env.debug env <| Options.Other "Rel" then
          BU.print_string "it's a pattern\n";
        let rhs = sn env rhs in
        let names_to_string fvs =
            List.map Print.bv_to_string (BU.set_elements fvs) |> String.concat ", "
        in
        let fvs1 = binders_as_bv_set (ctx_uv.ctx_uvar_binders @ lhs_binders) in
        let fvs2 = Free.names rhs in
        //if Env.debug env <| Options.Other "Rel" then
        //  BU.print4 "lhs \t= %s\n\
        //             FV(lhs) \t= %s\n\
        //             rhs \t= %s\n\
        //             FV(rhs) \t= %s\n"
        //               (flex_t_to_string lhs)
        //               (names_to_string fvs1)
        //               (Print.term_to_string rhs)
        //               (names_to_string fvs2);
        let uvars, occurs_ok, msg = occurs_check ctx_uv rhs in
        if not occurs_ok
        then giveup_or_defer env orig wl (Thunk.mkv <| "occurs-check failed: " ^ (Option.get msg))
        else if BU.set_is_subset_of fvs2 fvs1
        then let sol = mk_solution env lhs lhs_binders rhs in
             let wl = restrict_all_uvars env ctx_uv lhs_binders uvars wl in
             solve env (solve_prob orig None sol wl)
        else if wl.defer_ok
        then
          let msg = mklstr (fun () ->
                                BU.format3 "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           (names_to_string fvs2)
                                           (names_to_string fvs1)
                                           (Print.binders_to_string ", " (ctx_uv.ctx_uvar_binders @ lhs_binders))) in
          giveup_or_defer env orig wl msg
        else first_order orig env wl lhs rhs


      | _ -> //Not a pattern
        if wl.defer_ok
        then giveup_or_defer env orig wl (Thunk.mkv "Not a pattern")
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
      then giveup_or_defer env orig wl (Thunk.mkv "flex-flex subtyping")
      else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs

    | EQ ->
      if should_defer_flex_to_user_tac env wl lhs || should_defer_flex_to_user_tac env wl rhs
      then defer_to_user_tac env orig (flex_reason lhs ^", "^flex_reason rhs)wl
      else

      if wl.defer_ok
      && (not (is_flex_pat lhs)|| not (is_flex_pat rhs))
      then giveup_or_defer env orig wl (Thunk.mkv "flex-flex non-pattern")
      else
          match quasi_pattern env lhs, quasi_pattern env rhs with
          | Some (binders_lhs, t_res_lhs), Some (binders_rhs, t_res_rhs) ->
            let (Flex ({pos=range}, u_lhs, _)) = lhs in
            let (Flex (_, u_rhs, _)) = rhs in
            if UF.equiv u_lhs.ctx_uvar_head u_rhs.ctx_uvar_head
            && binders_eq binders_lhs binders_rhs
            then solve env (solve_prob orig None [] wl)
            else (* Given a flex-flex instance:
                    (x1..xn ..X  |- ?u : ts  -> tres) [y1  ... ym ]
                 ~  (x1..xn ..X' |- ?v : ts' -> tres) [y1' ... ym']

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
                                         (if u_lhs.ctx_uvar_should_check = Allow_untyped &&
                                             u_rhs.ctx_uvar_should_check = Allow_untyped
                                          then Allow_untyped
                                          else Strict)
                                         None in
                 let w_app = S.mk_Tm_app w (List.map (fun ({binder_bv=z}) -> S.as_arg (S.bv_to_name z)) zs) w.pos in
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
            giveup_or_defer env orig wl (Thunk.mkv "flex-flex: non-patterns")

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
        let solve_head_then wl k =
            if need_unif then k true wl
            else match solve_maybe_uinsts env orig head1 head2 wl with
            | USolved wl -> k true wl //(solve_prob orig None [] wl)
            | UFailed msg -> giveup env msg orig
            | UDeferred wl -> k false (defer_lit "universe constraints" orig wl)
        in
        let nargs = List.length args1 in
        if nargs <> List.length args2
        then giveup env
                    (mklstr
                      (fun () -> BU.format4 "unequal number of arguments: %s[%s] and %s[%s]"
                                     (Print.term_to_string head1)
                                     (args_to_string args1)
                                     (Print.term_to_string head2)
                                     (args_to_string args2)))
                    orig
        else
        if nargs=0 || U.eq_args args1 args2=U.Equal //special case: for easily proving things like nat <: nat, or greater_than i <: greater_than i etc.
        then if need_unif
             then solve_t env ({problem with lhs=head1; rhs=head2}) wl
             else solve_head_then wl (fun ok wl ->
                    if ok then solve env (solve_prob orig None [] wl)
                    else solve env wl)
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
              let mk_sub_probs wl =
                   let argp =
                       if need_unif
                       then List.zip ((head1, None)::args1) ((head2, None)::args2)
                       else List.zip args1 args2
                   in
                   let subprobs, wl =
                        List.fold_right
                            (fun ((a1, _), (a2, _)) (probs, wl) ->
                               let prob', wl = mk_problem wl [] orig a1 EQ a2 None "index" in
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
                  solve_head_then wl (fun ok wl ->
                      if not ok
                      then solve env wl
                      else let subprobs, wl = mk_sub_probs wl in
                           let formula = U.mk_conj_l (List.map (fun p -> p_guard p) subprobs) in
                           let wl = solve_prob orig (Some formula) [] wl in
                           solve env (attempt subprobs wl))
              in
              let solve_sub_probs_no_smt env wl =
                  solve_head_then wl (fun ok wl ->
                      assert ok; //defer not allowed
                      let subprobs, wl = mk_sub_probs wl in
                      let formula = U.mk_conj_l (List.map (fun p -> p_guard p) subprobs) in
                      let wl = solve_prob orig (Some formula) [] wl in
                      solve env (attempt subprobs wl))
              in
              let unfold_and_retry d env wl (prob, reason) =
                   if debug env <| Options.Other "Rel"
                   then BU.print2 "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                (prob_to_string env orig)
                                (Thunk.force reason);
                   match N.unfold_head_once env t1,
                         N.unfold_head_once env t2
                   with
                   | Some t1', Some t2' ->
                     let head1', _ = U.head_and_args t1' in
                     let head2', _ = U.head_and_args t2' in
                     begin
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
                     | _ ->
                       let torig' = {torig with lhs=t1'; rhs=t2'} in
                       if debug env <| Options.Other "Rel"
                       then BU.print1 "Unfolded and now trying %s\n"
                                      (prob_to_string env (TProb torig'));
                       solve_t env torig' wl
                     end
                   | _ ->
                     solve_sub_probs env wl //fallback to trying to solve with SMT on
              in
              let d =
                match delta_depth_of_term env head1 with
                | None -> None
                | Some d -> decr_delta_depth d
              in
              let treat_as_injective =
                match (U.un_uinst head1).n with
                | Tm_fvar fv ->
                  Env.fv_has_attr env fv Const.unifier_hint_injective_lid
                | _ -> false
              in
              begin
              match d with
              | Some d when wl.smt_ok && not treat_as_injective ->
                try_solve_without_smt_or_else env wl
                    solve_sub_probs_no_smt
                    (unfold_and_retry d)

              | _ -> //cannot be unfolded or no smt anyway; so just try to solve extensionally
                solve_sub_probs env wl

              end

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
            let (Flex (_t, uv, _args), wl) = destruct_flex_t scrutinee wl  in
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
            | Success (_, defer_to_tac, imps) ->
                let wl' = {wl' with attempting=[orig]} in
                (match solve env wl' with
                | Success (_, defer_to_tac', imps') ->
                  UF.commit tx;
                  Some (extend_wl wl (defer_to_tac@defer_to_tac') (imps@imps'))

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
                              match head_matches_delta env wl s t' with
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
        let m, o = head_matches_delta env wl t1 t2 in
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
              giveup_or_defer orig (Thunk.mkv "delaying match heuristic")

            | Inr (Some wl) ->
              solve env wl

            | Inr None ->
                if (may_relate head1 || may_relate head2) && wl.smt_ok
                then let guard, wl = guard_of_prob env wl problem t1 t2 in
                    solve env (solve_prob orig (Some guard) [] wl)
                else giveup env (mklstr (fun () -> BU.format4 "head mismatch (%s (%s) vs %s (%s))"
                                                  (Print.term_to_string head1)
                                                  (BU.dflt ""
                                                    (BU.bind_opt (delta_depth_of_term env head1)
                                                                 (fun x -> Some (Print.delta_depth_to_string x))))
                                                  (Print.term_to_string head2)
                                                  (BU.dflt ""
                                                    (BU.bind_opt (delta_depth_of_term env head2)
                                                                (fun x -> Some (Print.delta_depth_to_string x))))
                                                  )) orig
            end

        | (HeadMatch true, _) when problem.relation <> EQ ->
            //heads may only match after unification;
            //but we're not trying to unify them here
            //so, treat as a mismatch
            if wl.smt_ok
            then let guard, wl = guard_of_prob env wl problem t1 t2 in
                    solve env (solve_prob orig (Some guard) [] wl)
            else giveup env (mklstr (fun () -> BU.format2 "head mismatch for subtyping (%s vs %s)"
                                        (Print.term_to_string t1)
                                        (Print.term_to_string t2)))
                                orig

        | (_, Some (t1, t2)) -> //heads match after some delta steps
            solve_t env ({problem with lhs=t1; rhs=t2}) wl

        (* Need to maybe reunify the heads *)
        | (HeadMatch need_unif, None) ->
            rigid_heads_match env need_unif torig wl t1 t2

        | (FullMatch, None) ->
            rigid_heads_match env false torig wl t1 t2
    in
    (* <rigid_rigid_delta> *)

    let orig = TProb problem in
    def_check_prob "solve_t'.2" orig;
    if BU.physical_equality problem.lhs problem.rhs then solve env (solve_prob orig None [] wl) else
    let t1 = problem.lhs in
    let t2 = problem.rhs in
    def_check_closed_in (p_loc orig) "ref.t1" (List.map (fun b -> b.binder_bv) (p_scope orig)) t1;
    def_check_closed_in (p_loc orig) "ref.t2" (List.map (fun b -> b.binder_bv) (p_scope orig)) t2;
    let _ =
        if debug env (Options.Other "Rel")
        then BU.print4 "Attempting %s (%s vs %s); rel = (%s)\n" (string_of_int problem.pid)
                            (Print.tag_of_term t1 ^ "::" ^ Print.term_to_string t1)
                            (Print.tag_of_term t2 ^ "::" ^ Print.term_to_string t2)
                            (rel_to_string problem.relation)
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
            | bs -> mk_Total(mk (Tm_arrow(bs, c)) c.pos) in

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
            | bs -> mk (Tm_abs(bs, t, l)) t.pos in
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
            else begin
                let _, ty, _ = env.type_of ({env with lax=true; use_bv_sorts=true; expected_typ=None}) t in
                (* Find the WHNF ignoring refinements. Otherwise consider
                 *
                 * let myty1 = a -> Tot b
                 * let myty2 = f:myty1{whatever f}
                 *
                 * The WHNF of myty2 is not an arrow, and we would fail to eta-expand. *)
                let ty =
                    let rec aux ty =
                        let ty = N.unfold_whnf env ty in
                        match (SS.compress ty).n with
                        | Tm_refine _ -> aux (U.unrefine ty)
                        | _ -> ty
                    in aux ty
                in
                let r = N.eta_expand_with_type env t ty in
                if Env.debug wl.tcenv <| Options.Other "Rel" then
                  BU.print3 "force_eta of (%s) at type (%s) = %s\n" (Print.term_to_string t) (Print.term_to_string (N.unfold_whnf env ty)) (Print.term_to_string r);
                r
            end
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
                   else giveup env (Thunk.mkv "head tag mismatch: RHS is an abstraction") orig
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
            match head_matches_delta env wl x1.sort x2.sort with
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
                def_check_closed_in (p_loc orig) "ref.1" (List.map (fun b -> b.binder_bv) (p_scope orig)) (p_guard base_prob);
                def_check_closed_in (p_loc orig) "ref.2" (List.map (fun b -> b.binder_bv) (p_scope orig)) impl;
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
             let tx = UF.new_transaction () in
             (* We set wl_implicits to false, since in the success case we will
              * extend the original wl with the extra implicits we get, and we
              * do not want to duplicate the existing ones. *)
             match solve env ({wl with defer_ok=false; wl_implicits=[];
                                       attempting=[ref_prob]; wl_deferred=[]}) with
             | Failed (prob, msg) ->
               UF.rollback tx;
               if ((not env.uvar_subtyping && has_uvars)
                   || not wl.smt_ok)
                   && not env.unif_allow_ref_guards // if unif_allow_ref_guards is on, we don't give up
               then giveup env msg prob
               else fallback()

             | Success (_, defer_to_tac, imps) ->
               UF.commit tx;
               let guard =
                   U.mk_conj (p_guard base_prob)
                             (p_guard ref_prob |> guard_on_element wl problem x1) in
               let wl = solve_prob orig (Some guard) [] wl in
               let wl = {wl with ctr=wl.ctr+1} in
               let wl = extend_wl wl defer_to_tac imps in
               solve env (attempt [base_prob] wl)
        else fallback()

      (* flex-flex *)
      | Tm_uvar _,                Tm_uvar _
      | Tm_app({n=Tm_uvar _}, _), Tm_uvar _
      | Tm_uvar _,                Tm_app({n=Tm_uvar _}, _)
      | Tm_app({n=Tm_uvar _}, _), Tm_app({n=Tm_uvar _}, _) ->
      (* In the case that we have the same uvar on both sides, we cannot
       * simply call destruct_flex_t on them, and instead we need to do
       * both ensure_no_uvar_subst calls before destructing.
       *
       * Calling destruct_flex_t would (potentially) first solve the
       * head uvar to a fresh one and then return the new one. So, if we
       * we were calling destruct_flex_t directly, the second call will
       * solve the uvar returned by the first call. We would then pass
       * it to to solve_t_flex_flex, causing a crash.
       *
       * See issue #1616. *)
        let t1, wl = ensure_no_uvar_subst t1 wl in
        let t2 = U.canon_app t2 in
        (* ^ This canon_app call is needed for the incredibly infrequent case
         * where t2 is a Tm_app, its head uvar matches that of t1,
         * *and* the uvar is solved to an application by the previous
         * ensure_no_uvar_subst call. In that case, we get a nested application
         * in t2, and the call below would raise an error. *)
        let t2, wl = ensure_no_uvar_subst t2 wl in
        let f1 = destruct_flex_t' t1 in
        let f2 = destruct_flex_t' t2 in
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
        let rec solve_branches wl brs1 brs2 : option<(list<(binders * prob)> * worklist)> =
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
                        Some ([scope, p], wl))
                (fun (wprobs, wl) ->

                (* Branch body *)
                // GM: Could use problem.relation here instead of EQ?
                let prob, wl = mk_t_problem wl scope orig e1 EQ e2 None "branch body" in
                if Env.debug wl.tcenv <| Options.Other "Rel"
                then BU.print2 "Created problem for branches %s with scope %s\n"
                                        (prob_to_string env prob)
                                        (Print.binders_to_string ", " scope);
                BU.bind_opt (solve_branches wl rs1 rs2) (fun (r, wl) ->
                Some ((scope, prob)::(wprobs @ r), wl)))

            | [], [] -> Some ([], wl)
            | _ -> None
        in
        begin match solve_branches wl brs1 brs2 with
        | None ->
            if wl.smt_ok
            then by_smt ()
            else giveup env (Thunk.mkv "Tm_match branches don't match") orig
        | Some (sub_probs, wl) ->
            let sc_prob, wl = mk_t_problem wl [] orig s1 EQ s2 None "match scrutinee" in
            let sub_probs = ([], sc_prob)::sub_probs in
            let formula = U.mk_conj_l (List.map (fun (scope, p) -> close_forall wl.tcenv scope (p_guard p)) sub_probs) in
            let tx = UF.new_transaction () in
            let wl = solve_prob orig (Some formula) [] wl in
            begin match solve env (attempt (List.map snd sub_probs) ({wl with smt_ok = false})) with
            | Success (ds, ds', imp) ->
                UF.commit tx;
                Success (ds, ds', imp)
            | Failed _ ->
                UF.rollback tx;
                if wl.smt_ok
                then by_smt ()
                else giveup env (Thunk.mkv "Could not unify matches without SMT") orig
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
            let t1 = norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.2" [Env.UnfoldUntil delta_constant; Env.Primops; Env.Beta; Env.Eager_unfolding; Env.Iota] env t1 in
            let t2 = norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.3" [Env.UnfoldUntil delta_constant; Env.Primops; Env.Beta; Env.Eager_unfolding; Env.Iota] env t2 in
            U.eq_tm t1 t2 = U.Equal
         in
         if (Env.is_interpreted env head1 || Env.is_interpreted env head2) //we have something like (+ x1 x2) =?= (- y1 y2)
           && problem.relation = EQ
           && no_free_uvars t1 // and neither term has any free variables
           && no_free_uvars t2
         then if not wl.smt_ok
              then if equal t1 t2
                   then solve env (solve_prob orig None [] wl)
                   else rigid_rigid_delta env problem wl head1 head2 t1 t2
              else let guard, wl =
                       if equal t1 t2
                       then None, wl
                       else let g, wl = mk_eq2 wl env orig t1 t2 in
                            Some g, wl
                   in
                   solve env (solve_prob orig guard [] wl)
         else rigid_rigid_delta env problem wl head1 head2 t1 t2

      | Tm_let _, Tm_let _ ->
         // For now, just unify if they syntactically match
         if U.term_eq t1 t2
         then solve env (solve_prob orig None [] wl)
         else giveup env (Thunk.mkv "Tm_let mismatch") orig

      | Tm_let _, _
      | _, Tm_let _ ->
         raise_error (Errors.Fatal_UnificationNotWellFormed, BU.format4 "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                            (Print.tag_of_term t1) (Print.tag_of_term t2)
                            (Print.term_to_string t1) (Print.term_to_string t2)) t1.pos

      | _ -> giveup env (Thunk.mkv "head tag mismatch") orig

and solve_c (env:Env.env) (problem:problem<comp>) (wl:worklist) : solution =
    let c1 = problem.lhs in
    let c2 = problem.rhs in
    let orig = CProb problem in
    let sub_prob : worklist -> term -> rel -> term -> string -> prob * worklist =
        fun wl t1 rel t2 reason -> mk_t_problem wl [] orig t1 rel t2 None reason in

    let solve_eq c1_comp c2_comp g_lift =
        let _ = if Env.debug env <| Options.Other "EQ"
                then BU.print2 "solve_c is using an equality constraint (%s vs %s)\n"
                            (Print.comp_to_string (mk_Comp c1_comp))
                            (Print.comp_to_string (mk_Comp c2_comp)) in
        if not (lid_equals c1_comp.effect_name c2_comp.effect_name)
        then giveup env (mklstr (fun () -> BU.format2 "incompatible effects: %s <> %s"
                                        (Print.lid_to_string c1_comp.effect_name)
                                        (Print.lid_to_string c2_comp.effect_name))) orig
        else if List.length c1_comp.effect_args <> List.length c2_comp.effect_args
        then giveup env (mklstr (fun () -> BU.format2 "incompatible effect arguments: %s <> %s"
                                        (Print.args_to_string c1_comp.effect_args)
                                        (Print.args_to_string c2_comp.effect_args))) orig
        else
             let univ_sub_probs, wl =
               List.fold_left2 (fun (univ_sub_probs, wl) u1 u2 ->
                 let p, wl = sub_prob wl
                   (S.mk (S.Tm_type u1) Range.dummyRange)
                   EQ
                   (S.mk (S.Tm_type u2) Range.dummyRange)
                   "effect universes" in
                 (univ_sub_probs@[p]), wl) ([], wl) c1_comp.comp_univs c2_comp.comp_univs in
             let ret_sub_prob, wl = sub_prob wl c1_comp.result_typ EQ c2_comp.result_typ "effect ret type" in
             let arg_sub_probs, wl =
                 List.fold_right2
                        (fun (a1, _) (a2, _) (arg_sub_probs, wl) ->
                           let p, wl = sub_prob wl a1 EQ a2 "effect arg" in
                           p::arg_sub_probs, wl)
                        c1_comp.effect_args
                        c2_comp.effect_args
                        ([], wl)
             in
             let sub_probs = univ_sub_probs@[ret_sub_prob]@(arg_sub_probs @ (g_lift.deferred |> List.map snd)) in
             let guard =
               let guard = U.mk_conj_l (List.map p_guard sub_probs) in
               match g_lift.guard_f with
               | Trivial -> guard
               | NonTrivial f -> U.mk_conj guard f in
             let wl = { wl with wl_implicits = g_lift.implicits@wl.wl_implicits } in
             let wl = solve_prob orig (Some guard) [] wl in
             solve env (attempt sub_probs wl)
    in

    let solve_layered_sub c1 c2 =
      if Env.debug env <| Options.Other "LayeredEffectsApp" then
        BU.print2 "solve_layered_sub c1: %s and c2: %s\n"
          (c1 |> S.mk_Comp |> Print.comp_to_string)
          (c2 |> S.mk_Comp |> Print.comp_to_string);

      // if Env.debug env <| Options.Other "LayeredEffects" then
      //   BU.print2 "solve_layered_sub after lift c1: %s and c2: %s\n"
      //     (c1 |> S.mk_Comp |> Print.comp_to_string)
      //     (c2 |> S.mk_Comp |> Print.comp_to_string);

      (*
       * M t1 i_1 ... i_n <: M t2 j_1 ... j_n (equality is simple, just unify the indices, as before)
       * We solve it using following sub-problems and guards:
       *
       * --> sub_probs_is: first, if any of the indices i_1 ... i_n are uvars,
       *                   we simply unify them with corresponding indices on the R.H.S
       *
       * Then we solve t1 <: t2 as a sub-problem
       *
       * Next, we lookup M.stronger_wp
       * let M.stronger_wp =
       *   (u, a:Type u -> (x_i:t_i) -> f:repr<u> a f_i_1 ... f_i_n -> PURE (repr<u> a g_i_1 ... g_i_n) wp)
       *
       * We first instantiate it with c2.comp_univs
       *
       * Next, we create uvars ?u_i for each binder x_i
       *   with subtitutions [a/c2.result_typ]@[x_j/?u_j] (forall j < i)
       *
       * let substs = [a/c2.result_typ]@[x_i/?u_i]
       *
       * --> f_sub_probs: unify f_i_i[substs] with indices of c1
       * --> g_sub_probs: unify g_i_i[substs] with indices of c2
       *
       * --> Add (wp[substs] (fun _ -> True)) to the guard
       *)

      if problem.relation = EQ
      then solve_eq c1 c2 Env.trivial_guard        
      else
        let r = Env.get_range env in

        let subcomp_name = BU.format2 "%s <: %s"
          (c1.effect_name |> Ident.ident_of_lid |> Ident.string_of_id)
          (c2.effect_name |> Ident.ident_of_lid |> Ident.string_of_id) in

        let lift_c1 (edge:edge) : comp_typ * guard_t =
          c1 |> S.mk_Comp |> edge.mlift.mlift_wp env
             |> (fun (c, g) -> U.comp_to_comp_typ c, g) in

        let c1, g_lift, stronger_t_opt, is_polymonadic =
          match Env.exists_polymonadic_subcomp env c1.effect_name c2.effect_name with
          | None ->
            (match Env.monad_leq env c1.effect_name c2.effect_name with
             | None -> c1, Env.trivial_guard, None, false
             | Some edge ->
               let c1, g_lift = lift_c1 edge in
               c1, g_lift,
               c2.effect_name
               |> Env.get_effect_decl env
               |> U.get_stronger_vc_combinator
               |> (fun ts -> Env.inst_tscheme_with ts c2.comp_univs |> snd |> Some),
               false)
          | Some t ->
            c1, Env.trivial_guard,
            Env.inst_tscheme_with t c2.comp_univs |> snd |> Some,
            true in

        if is_none stronger_t_opt
        then giveup env (mklstr (fun () -> BU.format2 "incompatible monad ordering: %s </: %s"
                                        (Print.lid_to_string c1.effect_name)
                                        (Print.lid_to_string c2.effect_name))) orig
        else
          let stronger_t = stronger_t_opt |> must in
          let wl = { wl with wl_implicits = g_lift.implicits@wl.wl_implicits } in

          //sub problems for uvar indices in c1
          let is_sub_probs, wl =
            if is_polymonadic then [], wl
            else
              let rec is_uvar t =
                match (SS.compress t).n with
                | Tm_uvar _ -> true
                | Tm_uinst (t, _) -> is_uvar t
                | Tm_app (t, _) -> is_uvar t
                | _ -> false in
              List.fold_right2 (fun (a1, _) (a2, _) (is_sub_probs, wl) ->
                if is_uvar a1
                then begin
                       if Env.debug env <| Options.Other "LayeredEffectsEqns" then
                       BU.print2 "Layered Effects teq (rel c1 index uvar) %s = %s\n"
                         (Print.term_to_string a1) (Print.term_to_string a2);
                       let p, wl = sub_prob wl a1 EQ a2 "l.h.s. effect index uvar" in
                       p::is_sub_probs, wl
                     end
                 else is_sub_probs, wl
              ) c1.effect_args c2.effect_args ([], wl) in

          //return type sub problem
          let ret_sub_prob, wl = sub_prob wl c1.result_typ problem.relation c2.result_typ "result type" in

          let stronger_t_shape_error s = BU.format3
            "Unexpected shape of stronger for %s, reason: %s (t:%s)"
            (Ident.string_of_lid c2.effect_name) s (Print.term_to_string stronger_t) in

          let a_b, rest_bs, f_b, stronger_c =
            match (SS.compress stronger_t).n with
            | Tm_arrow (bs, c) when List.length bs >= 2 ->
              let (bs', c) = SS.open_comp bs c in
              let a = List.hd bs' in
              let bs = List.tail bs' in
              let rest_bs, f_b = bs |> List.splitAt (List.length bs - 1)
                |> (fun (l1, l2) -> l1, List.hd l2) in
              a, rest_bs, f_b, c
            | _ ->
              raise_error (Errors.Fatal_UnexpectedExpressionType,
                stronger_t_shape_error "not an arrow or not enough binders") r in

          let rest_bs_uvars, g_uvars = Env.uvars_for_binders env rest_bs
            [NT (a_b.binder_bv, c2.result_typ)]
            (fun b -> BU.format3 "implicit for binder %s in subcomp of %s at %s"
              (Print.binder_to_string b) (Ident.string_of_lid c2.effect_name) (Range.string_of_range r)) r in

          let wl = { wl with wl_implicits = g_uvars.implicits@wl.wl_implicits } in  //AR: TODO: FIXME: using knowledge that g_uvars is only implicits

          let substs = List.map2
            (fun b t -> NT (b.binder_bv, t))
            (a_b::rest_bs) (c2.result_typ::rest_bs_uvars) in

          let f_sub_probs, wl =
            let f_sort_is = U.effect_indices_from_repr
              f_b.binder_bv.sort
              (Env.is_layered_effect env c1.effect_name)
              r (stronger_t_shape_error "type of f is not a repr type")
              |> List.map (SS.subst substs) in

            List.fold_left2 (fun (ps, wl) f_sort_i c1_i ->
              if Env.debug env <| Options.Other "LayeredEffectsEqns"
              then BU.print3 "Layered Effects (%s) %s = %s\n" subcomp_name
                     (Print.term_to_string f_sort_i) (Print.term_to_string c1_i);
              let p, wl = sub_prob wl f_sort_i EQ c1_i "indices of c1" in
              ps@[p], wl
            ) ([], wl) f_sort_is (c1.effect_args |> List.map fst) in

          let stronger_ct = stronger_c |> SS.subst_comp substs |> U.comp_to_comp_typ in

          let g_sub_probs, wl =
            let g_sort_is = U.effect_indices_from_repr
              stronger_ct.result_typ
              (Env.is_layered_effect env c2.effect_name)
              r (stronger_t_shape_error "subcomp return type is not a repr") in

            List.fold_left2 (fun (ps, wl) g_sort_i c2_i ->
              if Env.debug env <| Options.Other "LayeredEffectsEqns"
              then BU.print3 "Layered Effects (%s) %s = %s\n" subcomp_name
                     (Print.term_to_string g_sort_i) (Print.term_to_string c2_i);
              let p, wl = sub_prob wl g_sort_i EQ c2_i "indices of c2" in
              ps@[p], wl
            ) ([], wl) g_sort_is (c2.effect_args |> List.map fst) in

          let fml =
            let u, wp = List.hd stronger_ct.comp_univs, fst (List.hd stronger_ct.effect_args) in
            Env.pure_precondition_for_trivial_post env u stronger_ct.result_typ wp Range.dummyRange in

          let sub_probs = ret_sub_prob::(is_sub_probs@f_sub_probs@g_sub_probs@(g_lift.deferred |> List.map snd)) in
          let guard =
            let guard = U.mk_conj_l (List.map p_guard sub_probs) in
            match g_lift.guard_f with
            | Trivial -> guard
            | NonTrivial f -> U.mk_conj guard f in
          let wl = solve_prob orig (Some <| U.mk_conj guard fml) [] wl in
          solve env (attempt sub_probs wl) in

    let solve_sub c1 edge c2 =
        if problem.relation <> SUB then
          failwith "impossible: solve_sub";
        let r = Env.get_range env in
        let lift_c1 () =
             let univs =
               match c1.comp_univs with
               | [] -> [env.universe_of env c1.result_typ]
               | x -> x in
             let c1 = { c1 with comp_univs = univs } in
             ({ c1 with comp_univs = univs })
             |> S.mk_Comp
             |> edge.mlift.mlift_wp env
             |> (fun (c, g) ->
                 if not (Env.is_trivial g)
                 then raise_error (Errors.Fatal_UnexpectedEffect,
                   BU.format2 "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                     (Ident.string_of_lid c1.effect_name) (Ident.string_of_lid c2.effect_name)) r
                 else U.comp_to_comp_typ c)
        in
        if not wl.repr_subcomp_allowed
        && not (lid_equals c1.effect_name c2.effect_name)
        && Env.is_reifiable_effect env c2.effect_name
                  // GM: What I would like to write instead of these two
                  // last conjuncts is something like
                  // [Option.isSome edge.mlift.mlift_term],
                  // but it seems that we always carry around a Some
                  // (fun _ _ e -> e) instead of a None even for
                  // primitive effects.
        then giveup env (mklstr (fun () -> BU.format2 "Cannot lift from %s to %s, it needs a lift\n"
                                            (string_of_lid c1.effect_name)
                                            (string_of_lid c2.effect_name)))
                        orig
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
                           norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.4"
                                           [Env.UnfoldUntil delta_constant; Env.Weak; Env.HNF] env
                                           (Env.reify_comp env (S.mk_Comp (lift_c1 ())) (env.universe_of env c1.result_typ))
                       in
                       let c2_repr =
                           norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.5"
                                           [Env.UnfoldUntil delta_constant; Env.Weak; Env.HNF] env
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
                         else let wpc1_2 = lift_c1 () |> (fun ct -> List.hd ct.effect_args) in
                              if is_null_wp_2
                              then let _ = if debug env <| Options.Other "Rel"
                                           then BU.print_string "Using trivial wp ... \n" in
                                   let c1_univ = env.universe_of env c1.result_typ in
                                   let trivial =
                                     match c2_decl |> U.get_wp_trivial_combinator with
                                     | None -> failwith "Rel doesn't yet handle undefined trivial combinator in an effect"
                                     | Some t -> t in
                                   mk (Tm_app (inst_effect_fun_with [c1_univ] env c2_decl trivial,
                                               [as_arg c1.result_typ;
                                                wpc1_2])) r
                              else let c2_univ = env.universe_of env c2.result_typ in
                                   let stronger = c2_decl |> U.get_stronger_vc_combinator in
                                   mk (Tm_app(inst_effect_fun_with [c2_univ] env c2_decl stronger,
                                              [as_arg c2.result_typ;
                                               as_arg wpc2;
                                               wpc1_2])) r in
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
         | GTotal (t1, _), Total (t2, _) when (Env.non_informative env t2) ->
            solve_t env (problem_using_guard orig t1 problem.relation t2 None "result type") wl

         | GTotal _, Total _ ->
            giveup env (Thunk.mkv "incompatible monad ordering: GTot </: Tot")  orig

         | Total  (t1, _), Total  (t2, _)
         | GTotal (t1, _), GTotal (t2, _) -> //rigid-rigid 1
            solve_t env (problem_using_guard orig t1 problem.relation t2 None "result type") wl

         | Total  (t1, _), GTotal (t2, _) when problem.relation = SUB ->
            solve_t env (problem_using_guard orig t1 problem.relation t2 None "result type") wl

         | Total  (t1, _), GTotal (t2, _) ->
            giveup env (Thunk.mkv "GTot =/= Tot") orig

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
                      solve_eq c1_comp c2_comp Env.trivial_guard
                 else begin
                    let c1 = Env.unfold_effect_abbrev env c1 in
                    let c2 = Env.unfold_effect_abbrev env c2 in
                    if debug env <| Options.Other "Rel" then BU.print2 "solve_c for %s and %s\n" (string_of_lid c1.effect_name) (string_of_lid c2.effect_name);
                    if Env.is_layered_effect env c2.effect_name then solve_layered_sub c1 c2
                    else
                      match Env.monad_leq env c1.effect_name c2.effect_name with
                      | None ->
                       giveup env (mklstr (fun () -> BU.format2 "incompatible monad ordering: %s </: %s"
                                              (Print.lid_to_string c1.effect_name)
                                              (Print.lid_to_string c2.effect_name))) orig
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
      let carry defs = List.map (fun (msg, x) -> msg ^ ": " ^ prob_to_string env x) defs |> String.concat ",\n" in
      let imps = print_pending_implicits g in
      BU.format5 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
        form (carry g.deferred) (carry g.deferred_to_tac)
        (ineqs_to_string g.univ_ineqs) imps

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

let solve_and_commit env probs err
  : option<(deferred * deferred * implicits)> =
  let tx = UF.new_transaction () in

  if Env.debug env <| Options.Other "RelBench" then
    BU.print1 "solving problems %s {\n"
      (FStar.Common.string_of_list (fun p -> string_of_int (p_pid p)) probs.attempting);
  let (sol, ms) = BU.record_time (fun () -> solve env probs) in
  if Env.debug env <| Options.Other "RelBench" then
    BU.print1 "} solved in %s ms\n" (string_of_int ms);

  match sol with
    | Success (deferred, defer_to_tac, implicits) ->
      let ((), ms) = BU.record_time (fun () -> UF.commit tx) in
      if Env.debug env <| Options.Other "RelBench" then
        BU.print1 "committed in %s ms\n" (string_of_int ms);
      Some (deferred, defer_to_tac, implicits)
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
      let f = norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
              [Env.Beta; Env.Eager_unfolding; Env.Simplify; Env.Primops; Env.NoFullNorm] env f in
      if Env.debug env <| Options.Other "Simplification" then BU.print1 "Simplified guard to %s\n" (Print.term_to_string f);
      let f = match (U.unmeta f).n with
        | Tm_fvar fv when S.fv_eq_lid fv Const.true_lid -> Trivial
        | _ -> NonTrivial f in
      {g with guard_f=f}

let with_guard env prob dopt =
    match dopt with
    | None -> None
    | Some (deferred, defer_to_tac, implicits) ->
      Some <| simplify_guard env
                ({guard_f=(p_guard prob |> NonTrivial);
                  deferred=deferred;
                  deferred_to_tac=defer_to_tac;
                  univ_ineqs=([], []);
                  implicits=implicits})

let with_guard_no_simp env prob dopt = match dopt with
    | None -> None
    | Some (deferred, defer_to_tac, implicits) ->
      Some ({guard_f=(p_guard prob |> NonTrivial);
             deferred=deferred;
             deferred_to_tac=defer_to_tac;
             univ_ineqs=([], []);
             implicits=implicits})

let try_teq smt_ok env t1 t2 : option<guard_t> =
     if debug env <| Options.Other "Rel" then
       BU.print2 "try_teq of %s and %s {\n" (Print.term_to_string t1) (Print.term_to_string t2);
     let prob, wl = new_t_problem (empty_worklist env) env t1 EQ t2 None (Env.get_range env) in
     let g = with_guard env prob <| solve_and_commit env (singleton wl prob smt_ok) (fun _ -> None) in
     if debug env <| Options.Other "Rel" then
       BU.print1 "} res = %s\n" (FStar.Common.string_of_option (guard_to_string env) g);
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

(*
 * AR: It would be nice to unify it with teq, the way we do it for subtyping
 *     i.e. write a common function that uses a bound variable,
 *          and if the caller requires a prop, close over it, else abstract it
 *     But that may change the existing VCs shape a bit
 *)
let get_teq_predicate env t1 t2 =
     if debug env <| Options.Other "Rel" then
       BU.print2 "get_teq_predicate of %s and %s {\n" (Print.term_to_string t1) (Print.term_to_string t2);
     let prob, x, wl = new_t_prob (empty_worklist env) env t1 EQ t2 in
     let g = with_guard env prob <| solve_and_commit env (singleton wl prob true) (fun _ -> None) in
     if debug env <| Options.Other "Rel" then
       BU.print1 "} res teq predicate = %s\n" (FStar.Common.string_of_option (guard_to_string env) g);

    match g with
    | None -> None
    | Some g -> Some (abstract_guard (S.mk_binder x) g)

let subtype_fail env e t1 t2 =
    Errors.log_issue (Env.get_range env) (Err.basic_type_error env (Some e) t2 t1)

let sub_comp env c1 c2 =
  let rel = if env.use_eq then EQ else SUB in
  if debug env <| Options.Other "Rel" then
    BU.print3 "sub_comp of %s --and-- %s --with-- %s\n" (Print.comp_to_string c1) (Print.comp_to_string c2) (if rel = EQ then "EQ" else "SUB");
  let prob, wl = new_problem (empty_worklist env) env c1 rel c2 None (Env.get_range env) "sub_comp" in
  let wl = { wl with repr_subcomp_allowed = true } in
  let prob = CProb prob in
  def_check_prob "sub_comp" prob;
  let (r, ms) = BU.record_time
                  (fun () -> with_guard env prob <| solve_and_commit env (singleton wl prob true)  (fun _ -> None))
  in
  if Env.debug env <| Options.Other "RelBench" then
    BU.print4 "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n" (Print.comp_to_string c1) (Print.comp_to_string c2) (if rel = EQ then "EQ" else "SUB") (string_of_int ms);
  r

let solve_universe_inequalities' tx env (variables, ineqs) : unit =
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

let solve_universe_inequalities env ineqs : unit =
    let tx = UF.new_transaction () in
    solve_universe_inequalities' tx env ineqs;
    UF.commit tx

let try_solve_deferred_constraints defer_ok smt_ok deferred_to_tac_ok env (g:guard_t) =
   let fail (d,s) =
      let msg = explain env d s in
      raise_error (Errors.Fatal_ErrorInSolveDeferredConstraints, msg) (p_loc d)
   in
   let wl = {wl_of_guard env g.deferred with defer_ok=defer_ok
                                           ; smt_ok=smt_ok } in
   if Env.debug env <| Options.Other "Rel"
   then begin
         BU.print3 "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
                  (BU.string_of_bool defer_ok)
                  (wl_to_string wl)
                  (string_of_int (List.length g.implicits))
   end;
   let g =
     match solve_and_commit env wl fail with
     | Some (_::_, _, _) when not defer_ok ->
       failwith "Impossible: Unexpected deferred constraints remain"

     | Some (deferred, defer_to_tac, imps) ->
       {g with deferred=deferred; deferred_to_tac=g.deferred_to_tac@defer_to_tac; implicits=g.implicits@imps}

     | _ ->
       failwith "Impossible: should have raised a failure already"
   in
   solve_universe_inequalities env g.univ_ineqs;
   let g =
     if deferred_to_tac_ok
     then DeferredImplicits.solve_deferred_to_tactic_goals env g
     else g 
   in
   if Env.debug env <| Options.Other "ResolveImplicitsHook"
   then BU.print1 "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s\n"
          (guard_to_string env g);
   {g with univ_ineqs=([], [])}

let solve_deferred_constraints env (g:guard_t) =
    let defer_ok = false in
    let smt_ok = true in
    let deferred_to_tac_ok = true in
    try_solve_deferred_constraints defer_ok smt_ok deferred_to_tac_ok env g

let solve_non_tactic_deferred_constraints env (g:guard_t) =
    let defer_ok = false in
    let smt_ok = true in
    let deferred_to_tac_ok = false in
    try_solve_deferred_constraints defer_ok smt_ok deferred_to_tac_ok env g

// Discharge (the logical part of) a guard [g].
//
// The `use_smt` flag says whether to use the smt solver to discharge
// this guard
//
// - If use_smt = true, this function NEVER returns None, and can be
//   considered to have successfully discharged the guard. However,
//   it could have logged an SMT error. The VC (aka the logical part
//   of the guard) is preprocessed with tactics before discharging:
//   every subterm wrapped with `with_tactic` has the tactic run on it
//   and a separate VC is generated for it. They are then discharged
//   sequentially.
//
// - If use_smt = false, then None means could not discharge the guard
//   without using smt. The procedure is to just normalize and simplify
//   the VC and check that it is [True].
//
// In every case, when this function returns [Some g], then the logical
// part of [g] is [Trivial].
let discharge_guard' use_env_range_msg env (g:guard_t) (use_smt:bool) : option<guard_t> =
  let debug =
      (Env.debug env <| Options.Other "Rel")
    || (Env.debug env <| Options.Other "SMTQuery")
    || (Env.debug env <| Options.Other "Tac")
  in
  if Env.debug env <| Options.Other "ResolveImplicitsHook"
  then BU.print1 "///////////////////ResolveImplicitsHook: discharge_guard'\n\
                  guard = %s\n"
                  (guard_to_string env g);
  let g = 
    let defer_ok = false in
    let deferred_to_tac_ok = true in
    try_solve_deferred_constraints defer_ok use_smt deferred_to_tac_ok env g 
  in
  let ret_g = {g with guard_f = Trivial} in
  if not (Env.should_verify env) then Some ret_g
  // GM: ^ this doesn't look like the right place for this check.
  else
    match g.guard_f with
    | Trivial -> Some ret_g
    | NonTrivial vc ->
      if debug
      then Errors.diag (Env.get_range env)
                       (BU.format1 "Before normalization VC=\n%s\n" (Print.term_to_string vc));
      let vc =
        Profiling.profile
          (fun () -> N.normalize [Env.Eager_unfolding; Env.Simplify; Env.Primops] env vc)
          (Some (Ident.string_of_lid (Env.current_module env)))
          "FStar.TypeChecker.Rel.vc_normalization"
      in
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
                        ignore <| Options.set_options "--no_tactics";
                        let vcs = env.solver.preprocess env vc in
                        vcs |> List.map (fun (env, goal, opts) ->
                        env, norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.7" [Env.Simplify; Env.Primops] env goal, opts)
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

(*
 * Solve the uni-valued implicits
 *
 * For now we handle only unit and unit refinement typed implicits,
 *   we can later extend it to single constructor inductives
 *
 * This function gets the unresolved implicits from the main resolve_implicits'
 *   function
 *
 * It only sets the value of the implicit's ctx uvar in the UF graph
 * -- leaving their typechecking to resolve_implicits'
 *
 * E.g. for a ?u:squash phi, this will only set ?u=unit in the UF graph,
 *   and, as usual, resolve_implicits' will check that G |= phi
 *
 * It returns a boolean (true if at least one implicit was solved)
 *   and the set of new implicits, right now this set is same as imps,
 *   for inductives, this may later include implicits for pattern variables
 *)
 
let try_solve_single_valued_implicits env is_tac (imps:Env.implicits) : Env.implicits * bool =
  (*
   * Get the value of the implicit imp
   * Going forward, it can also return new implicits for the pattern variables
   *   (cf. the comment above about extending it to inductives)
   *)
  if is_tac then imps, false
  else
    let imp_value imp : option<term> =
      let ctx_u, r = imp.imp_uvar, imp.imp_range in
  
     let t_norm = N.normalize N.whnf_steps env ctx_u.ctx_uvar_typ in
    
      match (SS.compress t_norm).n with
      | Tm_fvar fv when S.fv_eq_lid fv Const.unit_lid ->
        r |> S.unit_const_with_range |> Some
     | Tm_refine (b, _) when U.is_unit b.sort ->
        r |> S.unit_const_with_range |> Some
     | _ -> None in

    let b = List.fold_left (fun b imp ->  //check that the imp is still unsolved
      if UF.find imp.imp_uvar.ctx_uvar_head |> is_none
      then match imp_value imp with
           | Some tm -> commit ([TERM (imp.imp_uvar, tm)]); true
           | None -> b
      else b) false imps in

    imps, b
  
let resolve_implicits' env is_tac g =
  let must_total, forcelax =
    if is_tac then false, true
    else (not env.phase1 && not env.lax), false in

  let rec unresolved ctx_u =
    match (Unionfind.find ctx_u.ctx_uvar_head) with
    | Some r ->
        begin match ctx_u.ctx_uvar_meta with
        | None -> false
        (* If we have a meta annotation, we recurse to see if the uvar
         * is actually solved, instead of being resolved to yet another uvar.
         * In that case, while we are keeping track of that uvar, we must not
         * forget the meta annotation in case this second uvar is not solved.
         * See #1561. *)
        | Some _ ->
            begin match (SS.compress r).n with
            | Tm_uvar (ctx_u', _) -> unresolved ctx_u'
            | _ -> false
            end
        end
    | None -> true
  in
  let rec until_fixpoint (acc: Env.implicits * bool) (implicits:Env.implicits) : Env.implicits =
    let out, changed = acc in
    match implicits with
    | [] ->
      if not changed
      then let out, changed = try_solve_single_valued_implicits env is_tac out in
           if changed then until_fixpoint ([], false) out
           else out
      else until_fixpoint ([], false) out
    | hd::tl ->
          let { imp_reason = reason; imp_tm = tm; imp_uvar = ctx_u; imp_range = r } = hd in
          if ctx_u.ctx_uvar_should_check = Allow_unresolved
          then until_fixpoint(out, true) tl
          else if unresolved ctx_u
          then begin match ctx_u.ctx_uvar_meta with
               | Some (Ctx_uvar_meta_tac (env_dyn, tau)) ->
                    let env : Env.env = FStar.Dyn.undyn env_dyn in
                    if Env.debug env (Options.Other "Tac") then
                        BU.print1 "Running tactic for meta-arg %s\n" (Print.ctx_uvar_to_string ctx_u);

                    let t =
                      Errors.with_ctx "Running tactic for meta-arg"
                        (fun () -> env.synth_hook env hd.imp_uvar.ctx_uvar_typ tau)
                    in
                    // let the unifier handle setting the variable
                    let extra =
                        match teq_nosmt env t tm with
                        | None -> failwith "resolve_implicits: unifying with an unresolved uvar failed?"
                        | Some g -> g.implicits
                    in
                    let ctx_u = { ctx_u with ctx_uvar_meta = None } in
                    let hd = { hd with imp_uvar = ctx_u } in
                    until_fixpoint (out, true) (extra @ tl)
               | _ ->
                    until_fixpoint (hd::out, changed) tl

               end
          else if ctx_u.ctx_uvar_should_check = Allow_untyped
          then until_fixpoint(out, true) tl
          else let env = {env with gamma=ctx_u.ctx_uvar_gamma} in
               let tm = norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.8" [Env.Beta] env tm in
               let env = if forcelax then {env with lax=true} else env in
               if Env.debug env <| Options.Other "Rel"
               then BU.print5 "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                               (Print.uvar_to_string ctx_u.ctx_uvar_head)
                               (Print.term_to_string tm)
                               (Print.term_to_string ctx_u.ctx_uvar_typ)
                               reason
                               (Range.string_of_range r);
               let g =
                 Errors.with_ctx (BU.format3 "While checking implicit %s set to %s of expected type %s"
                                               (Print.uvar_to_string ctx_u.ctx_uvar_head)
                                               (N.term_to_string env tm)
                                               (N.term_to_string env ctx_u.ctx_uvar_typ))
                                 (fun () -> env.check_type_of must_total env tm ctx_u.ctx_uvar_typ)
               in
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

let resolve_implicits env g =
    if Env.debug env <| Options.Other "ResolveImplicitsHook"
    then BU.print1 "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\n\
                    guard = %s\n"
                    (guard_to_string env g);
    resolve_implicits' env false g

let resolve_implicits_tac env g = resolve_implicits' env true  g

let force_trivial_guard env g =
    if Env.debug env <| Options.Other "ResolveImplicitsHook"
    then BU.print1 "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\n\
                    guard = %s\n"
                    (guard_to_string env g);
    let g = solve_deferred_constraints env g in
    let g = resolve_implicits env g in
    match g.implicits with
    | [] -> ignore <| discharge_guard env g
    | imp::_ -> raise_error (Errors.Fatal_FailToResolveImplicitArgument,
                           BU.format3 "Failed to resolve implicit argument %s of type %s introduced for %s"
                                (Print.uvar_to_string imp.imp_uvar.ctx_uvar_head)
                                (N.term_to_string env imp.imp_uvar.ctx_uvar_typ)
                                imp.imp_reason) imp.imp_range

let teq_force (env:env) (t1:typ) (t2:typ) : unit =
    force_trivial_guard env (teq env t1 t2)

let teq_nosmt_force (env:env) (t1:typ) (t2:typ) :bool =
    match teq_nosmt env t1 t2 with
    | None -> false
    | Some g ->
        force_trivial_guard env g;
        true

let layered_effect_teq env (t1:term) (t2:term) (reason:option<string>) : guard_t =
  if Env.debug env <| Options.Other "LayeredEffectsEqns"
  then BU.print3 "Layered Effect (%s) %s = %s\n"
         (if reason |> is_none then "_" else reason |> must)              
         (Print.term_to_string t1) (Print.term_to_string t2);
  teq env t1 t2  //AR: teq_nosmt?


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

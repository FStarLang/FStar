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

module FStarC.TypeChecker.Rel
open FStar.Pervasives
open FStarC.Effect
open FStarC.List
open FStar open FStarC
open FStarC
open FStarC.Util
open FStarC.Errors
open FStarC.Defensive
open FStarC.TypeChecker
open FStarC.Syntax
open FStarC.TypeChecker.Env
open FStarC.Syntax.Syntax
open FStarC.Syntax.Subst
open FStarC.Ident
open FStarC.TypeChecker.Common
open FStarC.Syntax
open FStarC.Common

open FStarC.Class.Deq
open FStarC.Class.Show
open FStarC.Class.Tagged
open FStarC.Class.Setlike
open FStarC.Class.Listlike
open FStarC.Class.Monoid
module Setlike = FStarC.Class.Setlike
open FStarC.Class.Listlike
open FStarC.CList
module Listlike = FStarC.Class.Listlike

module BU = FStarC.Util //basic util
module U = FStarC.Syntax.Util
module S = FStarC.Syntax.Syntax
module SS = FStarC.Syntax.Subst
module N = FStarC.TypeChecker.Normalize
module UF = FStarC.Syntax.Unionfind
module PC = FStarC.Parser.Const
module FC = FStarC.Const
module TcComm = FStarC.TypeChecker.Common
module TEQ = FStarC.TypeChecker.TermEqAndSimplify
module CList = FStarC.CList

let dbg_Disch                = Debug.get_toggle "Disch"
let dbg_Discharge            = Debug.get_toggle "Discharge"
let dbg_EQ                   = Debug.get_toggle "EQ"
let dbg_ExplainRel           = Debug.get_toggle "ExplainRel"
let dbg_GenUniverses         = Debug.get_toggle "GenUniverses"
let dbg_ImplicitTrace        = Debug.get_toggle "ImplicitTrace"
let dbg_Imps                 = Debug.get_toggle "Imps"
let dbg_LayeredEffectsApp    = Debug.get_toggle "LayeredEffectsApp"
let dbg_LayeredEffectsEqns   = Debug.get_toggle "LayeredEffectsEqns"
let dbg_Rel                  = Debug.get_toggle "Rel"
let dbg_RelBench             = Debug.get_toggle "RelBench"
let dbg_RelDelta             = Debug.get_toggle "RelDelta"
let dbg_RelTop               = Debug.get_toggle "RelTop"
let dbg_ResolveImplicitsHook = Debug.get_toggle "ResolveImplicitsHook"
let dbg_Simplification       = Debug.get_toggle "Simplification"
let dbg_SMTQuery             = Debug.get_toggle "SMTQuery"
let dbg_Tac                  = Debug.get_toggle "Tac"

instance showable_implicit_checking_status : showable implicit_checking_status = {
  show = (function
          | Implicit_unresolved -> "Implicit_unresolved"
          | Implicit_checking_defers_univ_constraint -> "Implicit_checking_defers_univ_constraint"
          | Implicit_has_typing_guard (tm, typ) -> "Implicit_has_typing_guard");
}

let is_base_type env typ =
    let t = FStarC.TypeChecker.Normalize.unfold_whnf env typ in
    let head, args = U.head_and_args t in
    match (U.unascribe (U.un_uinst head)).n with
    | Tm_name _
    | Tm_fvar _
    | Tm_type _ -> true
    | _ -> false

let term_is_uvar (uv:ctx_uvar) (t:term) : bool =
  match (U.unascribe t).n with
  | Tm_uvar (uv', _) -> UF.equiv uv.ctx_uvar_head uv'.ctx_uvar_head
  | _ -> false

let binders_as_bv_set (bs:binders) : FlatSet.t bv =
  Setlike.from_list (List.map (fun b -> b.binder_bv) bs)

(* lazy string, for error reporting *)
type lstring = Thunk.t string

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
    | TERM of ctx_uvar & term
    | UNIV of S.universe_uvar & universe

type defer_ok_t =
  | NoDefer
  | DeferAny
  | DeferFlexFlexOnly

instance _ : showable defer_ok_t = {
  show = (function | NoDefer -> "NoDefer" | DeferAny -> "DeferAny" | DeferFlexFlexOnly -> "DeferFlexFlexOnly");
}

(* The set of problems currently being addressed *)
type worklist = {
    attempting:   probs;
    wl_deferred:  clist (int & deferred_reason & lstring & prob); //flex-flex cases, non patterns, and subtyping constraints involving a unification variable,
    wl_deferred_to_tac: clist (int & deferred_reason & lstring & prob); //problems that should be dispatched to a user-provided tactics
    ctr:          int;                          //a counter incremented each time we extend subst, used to detect if we've made progress
    defer_ok:     defer_ok_t;                   //whether or not carrying constraints is ok---at the top-level, this flag is NoDefer
    smt_ok:       bool;                         //whether or not falling back to the SMT solver is permitted
    umax_heuristic_ok: bool;                    //whether or not it's ok to apply a structural match on umax us = umax us'
    tcenv:        Env.env;                      //the top-level environment on which Rel was called
    wl_implicits: implicits_t;                  //additional uvars introduced
    repr_subcomp_allowed:bool;                  //whether subtyping of effectful computations
                                                //with a representation (which need a monadic lift)
                                                //is allowed; disabled by default, enabled in
                                                //sub_comp which is called by the typechecker, and
                                                //will insert the appropriate lifts.
    typeclass_variables: RBSet.t ctx_uvar     //variables that will be solved by typeclass instantiation
}

(* A NOTE ON ENVIRONMENTS

At many points during unification, we need to produce a typechecking
environment (Env.env) in order to call into functions such as type_of,
universe_of, and normalization. Hence, it is important to respect
scoping, particularly so after the removal of the use_bv_sorts flag.

Functions in this module used to explicitly pass around an Env.env, and
used that to call into Tc/Norm. However, while some of them pushed
binders as needed, some of them did not, and the result was a flurry of
subtle scoping bugs. And while those were fixed, we decided to just be
more principled.

The worklist, threaded through almost all functions, contains the
top-level environment on which the unifier was called. Problems
contain a unification variable with a gamma inside. Hence, to get
an environment, we use `p_env` below which reconstructs it from the
worklist's tcenv and a problem's uvar. This makes sure it is in-sync
with the problem being tackled. The uses of push_bv/push_binder should
be few.
*)

let as_deferred (wl_def:clist (int & deferred_reason & lstring & prob)) : deferred =
  CList.map (fun (_, reason, m, p) -> reason, Thunk.force m, p) wl_def

let as_wl_deferred wl (d:deferred): clist (int & deferred_reason & lstring & prob) =
  CList.map (fun (reason, m, p) -> wl.ctr, reason, Thunk.mkv m, p) d

(* --------------------------------------------------------- *)
(* <new_uvar> Generating new unification variables/patterns  *)
(* --------------------------------------------------------- *)
let new_uvar reason wl r gamma binders k should_check meta : ctx_uvar & term & worklist =
    let decoration = {
             uvar_decoration_typ = k;
             uvar_decoration_should_check = should_check;
             uvar_decoration_typedness_depends_on = [];
             uvar_decoration_should_unrefine = false;
        }
    in
    let ctx_uvar = {
         ctx_uvar_head=UF.fresh decoration r;
         ctx_uvar_gamma=gamma;
         ctx_uvar_binders=binders;
         ctx_uvar_reason=reason;
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
    if !dbg_ImplicitTrace then
      BU.print1 "Just created uvar (Rel) {%s}\n" (show ctx_uvar.ctx_uvar_head);
    ctx_uvar, t, {wl with wl_implicits = cons imp wl.wl_implicits}

let copy_uvar u (bs:binders) t wl =
  let env = {wl.tcenv with gamma = u.ctx_uvar_gamma } in
  let env = Env.push_binders env bs in
  new_uvar ("copy:"^u.ctx_uvar_reason) wl u.ctx_uvar_range env.gamma
           (Env.all_binders env) t
           (U.ctx_uvar_should_check u)
           u.ctx_uvar_meta

(* --------------------------------------------------------- *)
(* </new_uvar>                                               *)
(* --------------------------------------------------------- *)

(* Types used in the output of the solver *)

type solution =
  | Success of deferred & deferred & implicits_t
  | Failed  of prob & lstring

let extend_wl (wl:worklist) (defers:deferred) (defer_to_tac:deferred) (imps:implicits_t) =
  {wl with wl_deferred=wl.wl_deferred ++ as_wl_deferred wl defers;
           wl_deferred_to_tac=wl.wl_deferred_to_tac ++  as_wl_deferred wl defer_to_tac;
           wl_implicits=wl.wl_implicits ++ imps}

type variance =
    | COVARIANT
    | CONTRAVARIANT
    | INVARIANT

type tprob = problem typ
type cprob = problem comp
type problem_t 'a = problem 'a

(* --------------------------------------------------------- *)
(* </type defs>                                              *)
(* --------------------------------------------------------- *)

(* ------------------------------------------------*)
(* <prob/problem ops>                              *)
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
let p_scope prob =
   let r = match prob with
   | TProb p -> p.logical_guard_uvar.ctx_uvar_binders @ (match p_element prob with | None -> [] | Some x -> [S.mk_binder x])
   | CProb p -> p.logical_guard_uvar.ctx_uvar_binders @ (match p_element prob with | None -> [] | Some x -> [S.mk_binder x])
   in
   (* def_scope_wf "p_scope" (p_loc prob) r; *)
   r
let p_guard_uvar = function
   | TProb p -> p.logical_guard_uvar
   | CProb p -> p.logical_guard_uvar
let p_env wl prob =
  (* Note: ctx_uvar_gamma should be an extension of tcenv.gamma,
   * since we created this uvar during this unification run. *)
  { wl.tcenv with gamma=(p_guard_uvar prob).ctx_uvar_gamma}

let p_guard_env wl prob =
  { wl.tcenv with gamma=(match p_element prob with | None -> [] | Some x -> [Binding_var x]) @ (p_guard_uvar prob).ctx_uvar_gamma}

(* ------------------------------------------------*)
(* </prob/problem ops>                             *)
(* ------------------------------------------------*)

(* ------------------------------------------------*)
(* <Defensive check>                               *)
(* ------------------------------------------------*)

let def_scope_wf msg rng r =
    if not (Options.defensive ()) then () else
    let rec aux prev next =
        match next with
        | [] -> ()
        | ({binder_bv=bv})::bs ->
          begin
            def_check_scoped rng msg prev bv.sort;
            aux (prev @ [bv]) bs
          end
    in aux [] r

instance hasBinders_prob : Class.Binders.hasBinders prob = {
  boundNames = (fun prob -> Setlike.from_list (List.map (fun b -> b.binder_bv) <| p_scope prob));
}

let def_check_term_scoped_in_prob msg prob phi =
    def_check_scoped #prob_t #term (p_loc prob) msg prob phi

let def_check_comp_scoped_in_prob msg prob phi =
    def_check_scoped #prob_t #comp (p_loc prob) msg prob phi

let def_check_prob msg prob =
    if not (Options.defensive ()) then () else
    let msgf m = msg ^ "." ^ string_of_int (p_pid prob) ^ "." ^ m in
    def_scope_wf (msgf "scope") (p_loc prob) (p_scope prob);
    def_check_term_scoped_in_prob (msgf "guard") prob (p_guard prob);
    match prob with
    | TProb p ->
        begin
        def_check_term_scoped_in_prob (msgf "lhs") prob p.lhs;
        def_check_term_scoped_in_prob (msgf "rhs") prob p.rhs
        end
    | CProb p ->
        begin
        def_check_comp_scoped_in_prob (msgf "lhs") prob p.lhs;
        def_check_comp_scoped_in_prob (msgf "rhs") prob p.rhs
        end

(* ------------------------------------------------*)
(* </Defensive checks>                             *)
(* ------------------------------------------------*)

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
            (show u)
            ("@" ^ show (fst s))
            (show args)
    | _ -> show t

let prob_to_string env prob =
  match prob with
  | TProb p ->
    BU.format "\n%s:\t%s \n\t\t%s\n\t%s\n\t(reason:%s) (logical:%s)\n" //\twith guard %s\n\telement= %s\n" //  (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
        [(BU.string_of_int p.pid);
         (term_to_string p.lhs);
         (rel_to_string p.relation);
         (term_to_string p.rhs);
         (match p.reason with | [] -> "" | r::_ -> r);
         (show p.logical)
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

let prob_to_string' (wl:worklist) (prob:prob) : string =
  let env = p_env wl prob in
  prob_to_string env prob

let uvi_to_string env = function
    | UNIV (u, t) ->
      let x = if (Options.hide_uvar_nums()) then "?" else UF.univ_uvar_id u |> string_of_int in
      BU.format2 "UNIV %s <- %s" x (show t)

    | TERM (u, t) ->
      let x = if (Options.hide_uvar_nums()) then "?" else UF.uvar_id u.ctx_uvar_head |> string_of_int in
      BU.format2 "TERM %s <- %s" x (N.term_to_string env t)
let uvis_to_string env uvis = FStarC.Common.string_of_list (uvi_to_string env) uvis

(* ------------------------------------------------*)
(* </Printing>                                     *)
(* ------------------------------------------------*)


(* ------------------------------------------------*)
(* <worklist ops> Operations on worklists          *)
(* ------------------------------------------------*)
let empty_worklist env = {
    attempting=[];
    wl_deferred=empty;
    wl_deferred_to_tac=empty;
    ctr=0;
    tcenv=env;
    defer_ok=DeferAny;
    smt_ok=true;
    umax_heuristic_ok=true;
    wl_implicits=empty;
    repr_subcomp_allowed=false;
    typeclass_variables = Setlike.empty();
}

let giveup wl (reason : lstring) prob =
    if !dbg_Rel then
        BU.print2 "Failed %s:\n%s\n" (Thunk.force reason) (prob_to_string' wl prob);
    Failed (prob, reason)

let giveup_lit wl (reason : string) prob =
    giveup wl (mklstr (fun () -> reason)) prob

(* ------------------------------------------------*)
(* </worklist ops>                                 *)
(* ------------------------------------------------*)

let singleton wl prob smt_ok     = {wl with attempting=[prob]; smt_ok = smt_ok}
let wl_of_guard env g            = {empty_worklist env with attempting=List.map (fun (_, _, p) -> p) g}
let defer reason msg prob wl     = {wl with wl_deferred= cons (wl.ctr, reason, msg, prob) wl.wl_deferred}
let defer_lit reason msg prob wl = defer reason (Thunk.mkv msg) prob wl
let attempt probs wl             =
    List.iter (def_check_prob "attempt") probs;
    {wl with attempting=probs@wl.attempting}

let mk_eq2 wl prob t1 t2 : term & worklist =
    let env = p_env wl prob in
    def_check_scoped t1.pos "mk_eq2.t1" env t1;
    def_check_scoped t2.pos "mk_eq2.t2" env t2;
    (* NS: Rather than introducing a new variable, it would be much preferable
            to simply compute the type of t1 here.
            Sadly, it seems to be way too expensive to call env.type_of here.
    *)
    // let t_type, u = U.type_u () in
    // let binders = Env.all_binders env in
    // let _, tt, wl = new_uvar "eq2" wl t1.pos env.gamma binders t_type (Allow_unresolved "eq2 type") None in
    let tt, _ = env.typeof_well_typed_tot_or_gtot_term env t1 false in
    let u = env.universe_of env tt in
    U.mk_eq2 u tt t1 t2, wl

let p_invert = function
   | TProb p -> TProb <| invert p
   | CProb p -> CProb <| invert p
let p_logical = function
   | TProb p -> p.logical
   | CProb p -> p.logical
let set_logical (b:bool) = function
   | TProb p -> TProb {p with logical=b}
   | CProb p -> CProb {p with logical=b}

let is_top_level_prob p = p_reason p |> List.length = 1
let next_pid =
    let ctr = BU.mk_ref 0 in
    fun () -> incr ctr; !ctr

(* Creates a subproblem of [orig], in a context extended with [scope]. *)
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
                 (Allow_untyped "logical guard")
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
             logical=p_logical orig;
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

let new_problem wl env lhs rel rhs (subject:option bv) loc reason =
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
               (Allow_untyped "logical guard")
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
    logical=false; (* use set_logical to set this *)
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
     logical = p_logical orig;
    } in
    def_check_prob reason (TProb p);
    p

let guard_on_element wl problem x phi : term =
    match problem.element with
        | None ->
          let tcenv = p_env wl (TProb problem) in
          let u = tcenv.universe_of tcenv x.sort in
          U.mk_forall u x phi
        | Some e -> Subst.subst [NT(x,S.bv_to_name e)] phi

let explain wl d (s : lstring) =
    if !dbg_ExplainRel || !dbg_Rel
    then BU.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
                       (Range.string_of_range <| p_loc d)
                       (prob_to_string' wl d)
                       (p_reason d |> String.concat "\n\t>")
                       (Thunk.force s)
    else let d = maybe_invert_p d in
         let rel = match p_rel d with
            | EQ -> "equal to"
            | SUB -> "a subtype of"
            | _ -> failwith "impossible" in
         let lhs, rhs = match d with
            | TProb tp -> Err.print_discrepancy (N.term_to_string (p_env wl d)) tp.lhs tp.rhs
            | CProb cp -> Err.print_discrepancy (N.comp_to_string (p_env wl d)) cp.lhs cp.rhs in
         BU.format3 "%s is not %s the expected type %s" lhs rel rhs

(* ------------------------------------------------*)
(* </prob ops>                                     *)
(* ------------------------------------------------*)


(* ------------------------------------------------*)
(* <uvi ops> Instantiating unification variables   *)
(* ------------------------------------------------*)

let occurs (uk:ctx_uvar) t =
    let uvars =
        Free.uvars t
        |> elems // Bad: order dependent
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
                        (show uk.ctx_uvar_head)
                        (show t)) in
    uvars, not occurs, msg

let occurs_full (uk:ctx_uvar) t =
    let uvars =
        Free.uvars_full t
        |> elems // Bad: order dependent
    in
    let occurs =
        (uvars
        |> BU.for_some (fun uv ->
           UF.equiv uv.ctx_uvar_head uk.ctx_uvar_head))
    in
    occurs

let set_uvar env u (should_check_opt:option S.should_check_uvar) t =
  // Useful for debugging uvars setting bugs
  // if !dbg_Rel
  // then (
  //   BU.print2 "Setting uvar %s to %s\n"
  //     (show u)
  //     (show t);
  //   match Unionfind.find u.ctx_uvar_head with
  //   | None -> ()
  //   | Some t ->
  //     BU.print2 "Uvar already set to %s\n%s\n"
  //       (show t)
  //       (BU.stack_dump());
  //     failwith "DIE"
  // );

  (match should_check_opt with
   | None -> ()
   | Some should_check ->
     UF.change_decoration u.ctx_uvar_head
       ({UF.find_decoration u.ctx_uvar_head with uvar_decoration_should_check=should_check}));

  if Options.defensive () then (
    if snd (occurs u t) then
      failwith "OCCURS BUG!"
  );

  U.set_uvar u.ctx_uvar_head t

let commit (env:env_t) (uvis:list uvi) = uvis |> List.iter (function
    | UNIV(u, t)      ->
      begin match t with
        | U_unif u' -> UF.univ_union u u'
        | _ -> UF.univ_change u t
      end
    | TERM(u, t) ->
      def_check_scoped #(list bv) #term t.pos "commit" (List.map (fun b -> b.binder_bv) u.ctx_uvar_binders) t;
      set_uvar env u None t
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
(* <normalization>                                 *)
(* ------------------------------------------------*)
let sn' env t       = SS.compress (N.normalize [Env.Beta; Env.Reify] env t) |> U.unlazy_emb
let sn env t =
  Profiling.profile
    (fun () ->
      sn' env t)
    (Some (Ident.string_of_lid (Env.current_module env)))
    "FStarC.TypeChecker.Rel.sn"
let norm_with_steps profiling_tag steps env t =
  Profiling.profile
    (fun () ->
      N.normalize steps env t)
    (Some (Ident.string_of_lid (Env.current_module env)))
    profiling_tag


let should_strongly_reduce t =
    let h, _ = t |> U.unascribe |> U.head_and_args in
    match (SS.compress h).n with
    | Tm_constant (FStarC.Const.Const_reify _) -> true
    | _ -> false

let whnf env t =
  let norm steps t =
    t |> U.unmeta
      |> N.normalize steps env
      |> SS.compress
      |> U.unlazy_emb in

  Profiling.profile
    (fun () ->
      let steps =
        (if should_strongly_reduce t
          then [Env.Exclude Env.Zeta; Env.UnfoldUntil delta_constant]
          else [Env.Weak; Env.HNF]) // GM: an explanation of this bit would be good, I just retained it
        @ [Env.Beta; Env.Reify; Env.Primops]
      in
      norm steps t)
    (Some (Ident.string_of_lid (Env.current_module env)))
    "FStarC.TypeChecker.Rel.whnf"

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
    "FStarC.TypeChecker.Rel.normalize_refinement"

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
        | Tm_refine {b=x; phi} ->
            if norm
            then (x.sort, Some(x, phi))
            else (match norm_refinement env t1 with
                 | {n=Tm_refine {b=x; phi}} -> (x.sort, Some(x, phi))
                 | tt -> failwith (BU.format2 "impossible: Got %s ... %s\n"
                                               (show tt)
                                               (tag_of tt))
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
        | Tm_unknown -> failwith (BU.format2 "impossible (outer): Got %s ... %s\n" (show t1) (tag_of t1)) in

   aux false (whnf env t1)

let base_and_refinement env t : term & option (bv & term) =
    base_and_refinement_maybe_delta false env t

let unrefine env t : term =
    base_and_refinement env t |> fst

let trivial_refinement t : bv & term =
    S.null_bv t, U.t_true

let as_refinement delta env t : bv & term =
    let t_base, refinement = base_and_refinement_maybe_delta delta env t in
    match refinement with
        | None -> trivial_refinement t_base
        | Some (x, phi) -> x, phi

let force_refinement (t_base, refopt) : term =
    let y, phi = match refopt with
        | Some (y, phi) -> y, phi
        | None -> trivial_refinement t_base in
    mk (Tm_refine {b=y; phi}) t_base.pos

(* ------------------------------------------------ *)
(* </normalization>                                 *)
(* ------------------------------------------------ *)

(* ------------------------------------------------ *)
(* <printing worklists>                             *)
(* ------------------------------------------------ *)

let wl_to_string wl =
  let probs_to_string (ps:list prob) = 
    List.map (prob_to_string' wl) ps |> String.concat "\n\t"
  in
  let cprobs_to_string (ps:clist prob) =
    (* meh ... *)
    CList.map (prob_to_string' wl) ps |> to_list |> String.concat "\n\t"
  in
  BU.format2 "{ attempting = [ %s ];\n\
                deferred = [ %s ] }\n"
              (probs_to_string wl.attempting)
              (cprobs_to_string (CList.map (fun (_, _, _, x) -> x) wl.wl_deferred))

instance showable_wl : showable worklist = {
  show = wl_to_string;
}

(* ------------------------------------------------ *)
(* </printing worklists>                            *)
(* ------------------------------------------------ *)

(* A flexible term: the full term,
 * its unification variable at the head,
 * and the arguments the uvar is applied to. *)
type flex_t =
  | Flex of (term & ctx_uvar & args)

let flex_reason (Flex (_, u, _)) = u.ctx_uvar_reason

let flex_uvar (Flex (_, u, _)) = u

let flex_uvar_has_meta_tac u =
  match u.ctx_uvar_meta with
  | Some (Ctx_uvar_meta_tac _) -> true
  | _ -> false

let flex_t_to_string (Flex (_, c, args)) =
    BU.format2 "%s [%s]" (show c) (show args)

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
 *
 * NB: This function only uses the environment for debugging flags,
 * so it's safe to pass wl.tcenv.
 *)
let ensure_no_uvar_subst env (t0:term) (wl:worklist)
  : term & worklist
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
      let gamma_aff, new_gamma = FStarC.Common.max_suffix (binding_not_affected_by s)
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
                         (U.arrow dom_binders (S.mk_Total (U.ctx_uvar_typ uv)))
                         (U.ctx_uvar_should_check uv)
                         uv.ctx_uvar_meta
        in

        (* Solve the old variable *)
        let args_sol = List.map U.arg_of_non_null_binder dom_binders in
        let sol = S.mk_Tm_app t_v args_sol t0.pos in
        if !dbg_Rel
        then BU.print2 "ensure_no_uvar_subst solving %s with %s\n"
               (show uv)
               (show sol);
        set_uvar env uv (Some Already_checked) sol;

        (* Make a term for the new uvar, applied to the substitutions of
         * the abstracted arguments, plus all the original arguments. *)
        let args_sol_s = List.map (fun (a, i) -> SS.subst' s a, i) args_sol in
        let t = S.mk_Tm_app t_v (args_sol_s @ args) t0.pos in
        t, wl
      end
    | _ ->
      failwith (BU.format3 "ensure_no_uvar_subst: expected a uvar at the head (%s-%s-%s)"
                           (tag_of t0)
                           (tag_of head)
                           (tag_of (SS.compress head)))

let no_free_uvars t = Setlike.is_empty (Free.uvars t) && Setlike.is_empty (Free.univs t)

(* Deciding when it's okay to issue an SMT query for
 * equating a term whose head symbol is `head` with another term
 *
 * NB: this function only uses env for checking delta_depths,
 * so it's fine to use wl.tcenv.
 *)
let rec may_relate_with_logical_guard env is_eq head =
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
         is_eq
       | _ -> false)
    | Tm_ascribed {tm=t}
    | Tm_uinst (t, _)
    | Tm_meta {tm=t} -> may_relate_with_logical_guard env is_eq t
    | _ -> false

let may_relate env prel head  = may_relate_with_logical_guard env (EQ? prel) head

(* Only call if ensure_no_uvar_subst was called on t before *)
let destruct_flex_t' t : flex_t =
    let head, args = U.head_and_args t in
    match (SS.compress head).n with
    | Tm_uvar (uv, s) ->
      Flex (t, uv, args)
    | _ -> failwith "Not a flex-uvar"

(* Destruct a term into its uvar head and arguments. The wl is only
used to track implicits. *)
let destruct_flex_t (t:term) wl : flex_t & worklist =
  (* ensure_no_uvar_subst only uses the environment for debugging
   * flags, so it's safe to pass wl.tcenv *)
  let t, wl = ensure_no_uvar_subst wl.tcenv t wl in
  (* If there's any substitution on the head of t, it must
   * have been made trivial by the call above, so
   * calling destruct_flex_t' is fine. *)
  destruct_flex_t' t, wl

(* ------------------------------------------------ *)
(* <solving problems>                               *)
(* ------------------------------------------------ *)

let u_abs (k : typ) (ys : binders) (t : term) : term =
    let (ys, t), (xs, c) = match (SS.compress k).n with
        | Tm_arrow {bs; comp=c} ->
          if List.length bs = List.length ys
          then (ys, t), SS.open_comp bs c
          else let ys', t, _ = U.abs_formals t in
               (ys@ys', t), U.arrow_formals_comp k
        | _ -> (ys, t), ([], S.mk_Total k) in
    if List.length xs <> List.length ys
    (* TODO : not putting any cflags here on the annotation... *)
    then //The annotation is imprecise, due to a discrepancy in currying/eta-expansions etc.;
         //causing a loss in precision for the SMT encoding
         U.abs ys t (Some (U.mk_residual_comp PC.effect_Tot_lid None []))
    else let c = Subst.subst_comp (U.rename_binders xs ys) c in
         U.abs ys t (Some (U.residual_comp_of_comp c))

let solve_prob' resolve_ok prob logical_guard uvis wl =
    def_check_prob "solve_prob'" prob;
    let phi = match logical_guard with
      | None -> U.t_true
      | Some phi -> phi in
    let assign_solution xs uv phi =
        if !dbg_Rel
        then BU.print3 "Solving %s (%s) with formula %s\n"
                            (string_of_int (p_pid prob))
                            (show uv)
                            (show phi);
        let phi = U.abs xs phi (Some (U.residual_tot U.ktype0)) in
        def_check_scoped (p_loc prob) ("solve_prob'.sol." ^ string_of_int (p_pid prob))
                         (List.map (fun b -> b.binder_bv) <| p_scope prob) phi;
        set_uvar wl.tcenv uv None phi
    in
    let uv = p_guard_uvar prob in
    let fail () =
        failwith (BU.format2 "Impossible: this instance %s has already been assigned a solution\n%s\n"
                              (show uv)
                              (show (p_guard prob)))
    in
    let args_as_binders args =
        args |>
        List.collect (fun (a, i) ->
            match (SS.compress a).n with
            | Tm_name x ->
              let q, attrs = U.bqual_and_attrs_of_aqual i in
              let pq, attrs = U.parse_positivity_attributes attrs in
              [S.mk_binder_with_attrs x q pq attrs]
            | _ ->
              fail();
              [])
    in
    let wl =
        let g = whnf (p_guard_env wl prob) (p_guard prob) in
        if not (is_flex g)
        then if resolve_ok
             then wl
             else (fail(); wl)
        else let (Flex (_, uv, args), wl)  = destruct_flex_t g wl in
             assign_solution (args_as_binders args) uv phi;
             wl
    in
    commit wl.tcenv uvis;
    {wl with ctr=wl.ctr + 1}

let extend_universe_solution pid sol wl =
    if !dbg_Rel
    then BU.print2 "Solving %s: with [%s]\n" (string_of_int pid)
                                             (uvis_to_string wl.tcenv sol);
    commit wl.tcenv sol;
    {wl with ctr=wl.ctr+1}

let solve_prob (prob : prob) (logical_guard : option term) (uvis : list uvi) (wl:worklist) : worklist =
    def_check_prob "solve_prob.prob" prob;
    BU.iter_opt logical_guard (def_check_term_scoped_in_prob "solve_prob.guard" prob);
    if !dbg_Rel
    then BU.print2 "Solving %s: with %s\n" (string_of_int <| p_pid prob)
                                           (uvis_to_string wl.tcenv uvis);
    solve_prob' false prob logical_guard uvis wl

(* ------------------------------------------------ *)
(* </solving problems>                              *)
(* ------------------------------------------------ *)


(* ------------------------------------------------ *)
(* <variable ops> common ops on variables           *)
(* ------------------------------------------------ *)

let rec maximal_prefix (bs:binders) (bs':binders) : binders & (binders & binders) =
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
    match List.last_opt bs with
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
 * NS: 03/2022 Question:  How do we know that t_t is well-formed in maximal_prefix(G_s, G_t)?
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
    let _, src', wl = new_uvar ("restricted " ^ (show src.ctx_uvar_head)) wl
      src.ctx_uvar_range g pfx t
      (U.ctx_uvar_should_check src)
      src.ctx_uvar_meta in
    set_uvar env src (Some Already_checked) (f src');
    wl in

  let bs = bs |> List.filter (fun ({binder_bv=bv1}) ->
    src.ctx_uvar_binders |> List.existsb (fun ({binder_bv=bv2}) -> S.bv_eq bv1 bv2) &&  //binder exists in G_t
    not (pfx |> List.existsb (fun ({binder_bv=bv2}) -> S.bv_eq bv1 bv2))) in  //but not in the maximal prefix

  if List.length bs = 0 then aux (U.ctx_uvar_typ src) (fun src' -> src')  //no abstraction over bs
  else begin
    aux
      (let t = U.ctx_uvar_typ src in t |> S.mk_Total |> U.arrow bs)  //bs -> Tot t_t
      (fun src' -> S.mk_Tm_app  //?u bs
        src'
        (bs |> S.binders_to_names |> List.map S.as_arg)
        src.ctx_uvar_range)
  end

let restrict_all_uvars env (tgt:ctx_uvar) (bs:binders) (sources:list ctx_uvar) wl : worklist =
  match bs with
  | [] ->
    let ctx_tgt = binders_as_bv_set tgt.ctx_uvar_binders in
    List.fold_right 
      (fun (src:ctx_uvar) wl ->
        let ctx_src = binders_as_bv_set src.ctx_uvar_binders in
        if subset ctx_src ctx_tgt
        then wl // no need to restrict source, it's context is included in the context of the tgt
        else restrict_ctx env tgt [] src wl)
      sources
      wl

  | _ ->
    List.fold_right (restrict_ctx env tgt bs) sources wl

let intersect_binders (g:gamma) (v1:binders) (v2:binders) : binders =
    let as_set (v:binders) : RBSet.t bv =
      v |> List.fold_left (fun out x -> add x.binder_bv out) (Setlike.empty ())
    in
    let v1_set = as_set v1 in
    let ctx_binders =
        List.fold_left (fun out b -> match b with Binding_var x -> add x out | _ -> out)
                        (Setlike.empty ())
                        g
    in
    let isect, _ =
        v2 |> List.fold_left (fun (isect, isect_set) b ->
            let x, imp = b.binder_bv, b.binder_qual in
            if not <| mem x v1_set
            then //definitely not in the intersection
                 isect, isect_set
            else //maybe in the intersect, if its type is only dependent on prior elements in the telescope
                 let fvs = Free.names x.sort in
                 if subset fvs isect_set
                 then b::isect, add x isect_set
                 else isect, isect_set)
        ([], ctx_binders) in
    List.rev isect

let binders_eq v1 v2 =
  List.length v1 = List.length v2
  && List.forall2 (fun ({binder_bv=a}) ({binder_bv=b}) -> S.bv_eq a b) v1 v2

let name_exists_in_binders x bs =
    BU.for_some (fun ({binder_bv=y}) -> S.bv_eq x y) bs

let pat_vars env ctx args : option binders =
    let rec aux seen args =
      match args with
      | [] -> Some (List.rev seen)
      | (arg, i)::args ->
        let hd = sn env arg in
        match hd.n with
        | Tm_name a ->
          if name_exists_in_binders a seen
          || name_exists_in_binders a ctx
          then None
          else let bq, attrs = U.bqual_and_attrs_of_aqual i in
               let pq, attrs = U.parse_positivity_attributes attrs in
               aux ((S.mk_binder_with_attrs a bq pq attrs)::seen) args
        | _ -> None
    in
    aux [] args

(* ------------------------------------------------ *)
(* </variable ops>                                  *)
(* ------------------------------------------------ *)

let string_of_match_result = function
    | MisMatch (d1, d2) -> "MisMatch " ^ show (d1, d2)
    | HeadMatch u -> "HeadMatch " ^ string_of_bool u
    | FullMatch -> "FullMatch"

instance showable_match_result = { show = string_of_match_result; }

let head_match = function
    | MisMatch(i, j) -> MisMatch(i, j)
    | HeadMatch true -> HeadMatch true
    | _ -> HeadMatch false

let universe_has_max env u =
  let u = N.normalize_universe env u in
  match u with
  | U_max _ -> true
  | _ -> false

let rec head_matches env t1 t2 : match_result =
  let t1 = U.unmeta t1 in
  let t2 = U.unmeta t2 in
  if !dbg_RelDelta then (
      BU.print2 "head_matches %s %s\n" (show t1) (show t2);
      BU.print2 "             %s  -- %s\n" (tag_of t1) (tag_of t2);
      ()
  );
  match t1.n, t2.n with
    | Tm_lazy ({lkind=Lazy_embedding _}), _ -> head_matches env (U.unlazy t1) t2
    |  _, Tm_lazy({lkind=Lazy_embedding _}) -> head_matches env t1 (U.unlazy t2)
    | Tm_lazy li1, Tm_lazy li2 ->
      if li1.lkind =? li2.lkind
      then HeadMatch false
      else MisMatch(None, None)

    | Tm_name x, Tm_name y -> if S.bv_eq x y then FullMatch else MisMatch(None, None)
    | Tm_fvar f, Tm_fvar g -> if S.fv_eq f g then FullMatch else MisMatch(Some (fv_delta_depth env f), Some (fv_delta_depth env g))
    | Tm_uinst (f, _), Tm_uinst(g, _) -> head_matches env f g |> head_match
    | Tm_constant (FC.Const_reify _), Tm_constant (FC.Const_reify _) -> FullMatch
    | Tm_constant (FC.Const_reify _), _
    | _, Tm_constant (FC.Const_reify _) -> HeadMatch true
    | Tm_constant c, Tm_constant d -> if FC.eq_const c d then FullMatch else MisMatch(None, None)

    | Tm_uvar (uv, _), Tm_uvar (uv', _) -> if UF.equiv uv.ctx_uvar_head uv'.ctx_uvar_head then FullMatch else MisMatch(None, None)

    | Tm_refine {b=x}, Tm_refine {b=y} -> head_matches env x.sort y.sort |> head_match

    | Tm_refine {b=x}, _  -> head_matches env x.sort t2 |> head_match
    | _, Tm_refine {b=x}  -> head_matches env t1 x.sort |> head_match

    | Tm_type _, Tm_type _
    | Tm_arrow _, Tm_arrow _ -> HeadMatch false

    | Tm_app {hd=head}, Tm_app {hd=head'} -> head_matches env head head' |> head_match
    | Tm_app {hd=head}, _ -> head_matches env head t2 |> head_match
    | _, Tm_app {hd=head} -> head_matches env t1 head |> head_match

    | Tm_let _, Tm_let _
    | Tm_match _, Tm_match _
    | Tm_quoted _, Tm_quoted _
    | Tm_abs _, Tm_abs _ -> HeadMatch true

    | _ ->
      (* GM: I am retaining this logic here. I think it is meant to disable
      unfolding of possibly-equational terms. This probably deserves a rework now
      with the .logical field. *)
      let maybe_dd (t:term) : option delta_depth =
        match (SS.compress t).n with
        | Tm_unknown
        | Tm_bvar _
        | Tm_name _
        | Tm_uvar _
        | Tm_let _
        | Tm_match _ -> None
        | _ -> Some (delta_depth_of_term env t)
      in
      MisMatch (maybe_dd t1, maybe_dd t2)

(* Does t1 head-match t2, after some delta steps? *)
let head_matches_delta env (logical:bool) smt_ok t1 t2 : (match_result & option (typ&typ)) =
    let base_steps =
      (if logical then [Env.DontUnfoldAttr [PC.tac_opaque_attr]] else []) @
      [Env.Primops; Env.Weak; Env.HNF]
    in
    let maybe_inline t =
        let head = U.head_of (unrefine env t) in
        if !dbg_RelDelta then
            BU.print2 "Head of %s is %s\n" (show t) (show head);
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
            if !dbg_RelDelta then
                BU.print1 "No definition found for %s\n" (show head);
            None
          | Some _ ->
            let basic_steps =
                (if logical then [Env.DontUnfoldAttr [PC.tac_opaque_attr]] else []) @
                [Env.UnfoldUntil delta_constant;
                 Env.Weak;
                 Env.HNF;
                 Env.Primops;
                 Env.Beta;
                 Env.Eager_unfolding;
                 Env.Iota]
            in
            let steps =
              if smt_ok then basic_steps
              else Env.Exclude Env.Zeta::basic_steps
                   //NS: added this to prevent unifier looping
                   //see bug606.fst
                   //should we always disable Zeta here?
            in
            let t' = norm_with_steps "FStarC.TypeChecker.Rel.norm_with_steps.1" steps env t in
            if TEQ.eq_tm env t t' = TEQ.Equal //if we didn't inline anything
            then None
            else let _ = if !dbg_RelDelta
                         then BU.print2 "Inlined %s to %s\n"
                                        (show t)
                                        (show t') in
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
     *
     * GM: Updated 2024/05/18 to check for a discrepancy in syntactic equality, instead of
     * eq_tm *not* returning Equal. We can have syntactically equal terms for which eq_tm
     * returns unknown, so this code would falsely claim progress. For instance, Tm_let
     * nodes are not handled by eq_tm and it always returns unknown. That should probably
     * be improved, but in either case I think we want a syntactic check here (which is
     * faster too) than eq_tm which is meant for decidable equality.
     *)
    let made_progress t t' =
      let head  = U.head_and_args t  |> fst in
      let head' = U.head_and_args t' |> fst in
      not (U.term_eq head head')
    in

    let rec aux retry n_delta t1 t2 =
        let r = head_matches env t1 t2 in
        if !dbg_RelDelta then
            BU.print3 "head_matches (%s, %s) = %s\n"
                (show t1)
                (show t2)
                (string_of_match_result r);
        let reduce_one_and_try_again (d1:delta_depth) (d2:delta_depth) =
          let d1_greater_than_d2 = Common.delta_depth_greater_than d1 d2 in
          let t1, t2, made_progress =
            if d1_greater_than_d2
            then let t1' = normalize_refinement (Env.UnfoldUntil d2 :: base_steps) env t1 in
                 t1', t2, made_progress t1 t1'
            else let t2' = normalize_refinement (Env.UnfoldUntil d1 :: base_steps) env t2 in
                 t1, t2', made_progress t2 t2' in
          if made_progress
          then aux retry (n_delta + 1) t1 t2
          else fail n_delta r t1 t2
        in

        let reduce_both_and_try_again (d:delta_depth) (r:match_result) =
          match Common.decr_delta_depth d with
          | None -> fail n_delta r t1 t2
          | Some d ->
            let t1' = normalize_refinement (Env.UnfoldUntil d :: base_steps) env t1 in
            let t2' = normalize_refinement (Env.UnfoldUntil d :: base_steps) env t2 in
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
    if !dbg_RelDelta then
        BU.print3 "head_matches_delta (%s, %s) = %s\n"
            (show t1) (show t2) (show r);
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
    r1 <> r2 &&
    rank_t_num r1 <= rank_t_num r2
let compress_tprob wl p =
  let env = p_env wl (TProb p) in
  {p with lhs=whnf env p.lhs; rhs=whnf env p.rhs}

let compress_cprob wl p =
  let whnf_c env c =
    match c.n with
    | Total ty -> S.mk_Total (whnf env ty)
    | _ -> c
  in
  let env = p_env wl (CProb p) in
  {p with lhs = whnf_c env p.lhs; rhs = whnf_c env p.rhs}

let compress_prob wl p =
    match p with
    | TProb p -> compress_tprob wl p |> TProb
    | CProb p -> compress_cprob wl p |> CProb

let rank wl pr : rank_t //the rank
                & prob   //the input problem, pre-processed a bit (the wl is needed for the pre-processing)
                =
   let prob = compress_prob wl pr |> maybe_invert_p in
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

let next_prob wl : option (prob & list prob & rank_t) =
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
          let rank, hd = rank wl hd in
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
    let wl = empty_worklist tcenv in
    let r, p = rank wl p in
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

    let rec filter_out_common_univs (u1:list universe) (u2:list universe) :(list universe & list universe) =
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
                                                   (show u1)
                                                   (show u2))
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
                                       (show u1)
                                       (show u2) msg) in

    match u1, u2 with
        | U_bvar _, _
        | U_unknown, _
        | _, U_bvar _
        | _, U_unknown -> failwith (BU.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                                        (show u1)
                                        (show u2))

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
          else let wl = extend_universe_solution pid_orig [UNIV(v1, u2)] wl in
               USolved wl

        | U_unif v1, u
        | u, U_unif v1 ->
          let u = norm_univ wl u in
          if occurs_univ v1 u
          then try_umax_components u1 u2
                (BU.format2 "Failed occurs check: %s occurs in %s" (show (U_unif v1)) (show u))
          else USolved (extend_universe_solution pid_orig [UNIV(v1, u)] wl)

        | U_max _, _
        | _, U_max _ ->
          if wl.defer_ok = DeferAny
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
let match_num_binders (bc1: (list 'a & (list 'a -> 'b)))
                      (bc2: (list 'a & (list 'a -> 'b)))
    : (list 'a & 'b) & (list 'a & 'b) =
    let (bs1, mk_cod1) = bc1 in
    let (bs2, mk_cod2) = bc2 in
    let rec aux (bs1 : list 'a) (bs2 : list 'a) : (list 'a & 'b) & (list 'a & 'b) =
        match bs1, bs2 with
        | x::xs, y::ys ->
            let ((xs, xr), (ys, yr)) = aux xs ys in
            ((x::xs, xr), (y::ys, yr))
        | xs, ys -> // at least one empty
            (([], mk_cod1 xs), ([], mk_cod2 ys))
    in
    aux bs1 bs2

let guard_of_prob (wl:worklist) (problem:tprob) (t1 : term) (t2 : term) : term & worklist =
   def_check_prob "guard_of_prob" (TProb problem);
   let env = p_env wl (TProb problem) in
    let has_type_guard t1 t2 =
        match problem.element with
        | Some t ->
            U.mk_has_type t1 (S.bv_to_name t) t2
        | None ->
            let x = S.new_bv None t1 in
            def_check_scoped t1.pos "guard_of_prob.universe_of" env t1;
            let u_x = env.universe_of env t1 in
            U.mk_forall u_x x (U.mk_has_type t1 (S.bv_to_name x) t2)
    in
    match problem.relation with
    | EQ     -> mk_eq2 wl (TProb problem) t1 t2
    | SUB    -> has_type_guard t1 t2, wl
    | SUBINV -> has_type_guard t2 t1, wl

let is_flex_pat = function
    | Flex (_, _, []) -> true
    | _ -> false

(** If the head uvar of the flex term is tagged with a `Ctx_uvar_meta_attr a`
    and if a term tagged with attribute `a` is in scope,
    then this problem should be deferred to a tactic *)
let should_defer_flex_to_user_tac (wl:worklist) (f:flex_t) =
  let (Flex (_, u, _)) = f in
  let b = DeferredImplicits.should_defer_uvar_to_user_tac wl.tcenv u in

  if !dbg_ResolveImplicitsHook then
    BU.print3 "Rel.should_defer_flex_to_user_tac for %s returning %s (env.enable_defer_to_tac: %s)\n"
      (show u) (show b) (show wl.tcenv.enable_defer_to_tac);

  b

(* <quasi_pattern>:
        Given a term (?u_(bs;t) e1..en)
        returns None in case the arity of the type t is less than n
        otherwise returns Some (x1 ... xn)
        where if ei is a variable distinct from bs and all the ej
            then xi = ei
            else xi is a fresh variable
    *)
let quasi_pattern env (f:flex_t) : option (binders & typ) =
    let (Flex (_, ctx_uvar, args)) = f in
    let t_hd = U.ctx_uvar_typ ctx_uvar in
    let ctx = ctx_uvar.ctx_uvar_binders in
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
                        let q, _ = U.bqual_and_attrs_of_aqual a_imp in
                        aux ((S.mk_binder_with_attrs
                               ({x with sort=formal.sort})
                               q
                               fml.binder_positivity
                               fml.binder_attrs) :: pat_binders) formals t_res args
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

let run_meta_arg_tac (env:env_t) (ctx_u:ctx_uvar) : term =
  match ctx_u.ctx_uvar_meta with
  | Some (Ctx_uvar_meta_tac tau) ->
    let env = { env with gamma = ctx_u.ctx_uvar_gamma } in
    if !dbg_Tac then
      BU.print1 "Running tactic for meta-arg %s\n" (show ctx_u);
    Errors.with_ctx "Running tactic for meta-arg"
      (fun () -> env.synth_hook env (U.ctx_uvar_typ ctx_u) tau)
  | _ ->
    failwith "run_meta_arg_tac must have been called with a uvar that has a meta tac"

let simplify_vc full_norm_allowed env t =
  if !dbg_Simplification then
    BU.print1 "Simplifying guard %s\n" (show t);
  let steps = [Env.Beta;
               Env.Eager_unfolding;
               Env.Simplify;
               Env.Primops;
               Env.Exclude Env.Zeta] in
  let steps = if full_norm_allowed then steps else Env.NoFullNorm::steps in
  let t' = norm_with_steps "FStarC.TypeChecker.Rel.simplify_vc" steps env t in
  if !dbg_Simplification then
    BU.print1 "Simplified guard to %s\n" (show t');
  t'

let __simplify_guard full_norm_allowed env g = match g.guard_f with
  | Trivial -> g
  | NonTrivial f ->
    let f = simplify_vc full_norm_allowed env f in
    let f = check_trivial f in
    { g with guard_f = f}

let simplify_guard env g = match g.guard_f with
  | Trivial -> g
  | NonTrivial f ->
    let f = simplify_vc false env f in
    let f = check_trivial f in
    { g with guard_f = f}

let simplify_guard_full_norm env g = match g.guard_f with
  | Trivial -> g
  | NonTrivial f ->
    let f = simplify_vc true env f in
    let f = check_trivial f in
    { g with guard_f = f}

//
// Apply substitutive indexed effects subcomp for an effect M
//
// bs: (opened) binders in the subcomp type
// subcomp_c: the computation type in the subcomp type (opened with bs)
// ct1 ct2: the two input computation types, both in M
// sub_prob: a function to create and add subproblems to the worklist
// num_effect_params: number of effect parameters in M
// wl: worklist
// subcomp_name and r1: for debugging purposes
//
// returns the (subcomp guard, new sub problems, worklist)
//
let apply_substitutive_indexed_subcomp (env:Env.env)
  (k:S.indexed_effect_combinator_kind)
  (bs:binders)
  (subcomp_c:comp)
  (ct1:comp_typ) (ct2:comp_typ)
  (sub_prob:worklist -> term -> rel -> term -> string -> prob & worklist)
  (num_effect_params:int)
  (wl:worklist)
  (subcomp_name:string)
  (r1:Range.range)

  : typ & list prob & worklist =

  //
  // We will collect the substitutions in subst,
  // bs will be the remaining binders (that are not in subst yet)
  //

  // first the a:Type binder
  let bs, subst =
    let a_b::bs = bs in
    bs,
    [NT (a_b.binder_bv, ct2.result_typ)] in

  //
  // If the effect has effect parameters:
  //   - peel those arguments off of ct1 and ct2,
  //   - add subproblems for their equality to the worklist
  //   - add substitutions for corresponding binders
  //
  let bs, subst, args1, args2, eff_params_sub_probs, wl =
    if num_effect_params = 0
    then bs, subst, ct1.effect_args, ct2.effect_args, [], wl
    else let split (l:list 'a) = List.splitAt num_effect_params l in
         let eff_params_bs, bs = split bs in
         let param_args1, args1 = split ct1.effect_args in
         let param_args2, args2 = split ct2.effect_args in

         let probs, wl = List.fold_left2 (fun (ps, wl) (t1, _) (t2, _) ->
           let p, wl = sub_prob wl t1 EQ t2 "effect params subcomp" in
           ps@[p], wl) ([], wl) param_args1 param_args2 in
         let param_subst = List.map2 (fun b (arg, _) ->
           NT (b.binder_bv, arg)) eff_params_bs param_args1 in
         bs, subst@param_subst, args1, args2, probs, wl in

  // add substitutions for the f computation
  let bs, subst =
    let f_bs, bs = List.splitAt (List.length args1) bs in
    let f_substs = List.map2 (fun f_b (arg, _) -> NT (f_b.binder_bv, arg)) f_bs args1 in
    bs,
    subst@f_substs in

  // add substitutions for the g computation
  let bs, subst, f_g_args_eq_sub_probs, wl =
    if Substitutive_combinator? k
    then begin
      let g_bs, bs = List.splitAt (List.length args2) bs in
      let g_substs = List.map2 (fun g_b (arg, _) -> NT (g_b.binder_bv, arg)) g_bs args2 in
      bs,
      subst@g_substs,
      [],
      wl
    end
    else if Substitutive_invariant_combinator? k
    then begin
      let probs, wl = List.fold_left2 (fun (ps, wl) (t1, _) (t2, _) ->
        let p, wl = sub_prob wl t1 EQ t2 "substitutive inv subcomp args" in
        ps@[p], wl) ([], wl) args1 args2 in
      bs, subst, probs, wl
    end
    else failwith "Impossible (rel.apply_substitutive_indexed_subcomp unexpected k" in

  // peel off the f:repr a is binder from bs
  let bs = List.splitAt (List.length bs - 1) bs |> fst in

  // for the binders in bs, create uvars, and add their substitutions
  let subst, wl =
    List.fold_left (fun (ss, wl) b ->
      let [uv_t], g = Env.uvars_for_binders env [b] ss
        (fun b ->
         if !dbg_LayeredEffectsApp
         then BU.format3 "implicit var for additional binder %s in subcomp %s at %s"
                (show b)
                subcomp_name
                (Range.string_of_range r1)
         else "apply_substitutive_indexed_subcomp") r1 in
      ss@[NT (b.binder_bv, uv_t)],
      {wl with wl_implicits=g.implicits ++ wl.wl_implicits}) (subst, wl) bs in

  // apply the substitutions to subcomp_c,
  //   and get the precondition from the PURE wp
  let subcomp_ct = subcomp_c |> SS.subst_comp subst |> Env.comp_to_comp_typ env in

  let fml =
    let u, wp = List.hd subcomp_ct.comp_univs, fst (List.hd subcomp_ct.effect_args) in
    Env.pure_precondition_for_trivial_post env u subcomp_ct.result_typ wp Range.dummyRange in

  fml,
  eff_params_sub_probs@f_g_args_eq_sub_probs,
  wl

//
// Apply ad-hoc indexed effects subcomp for an effect M
//
// bs: (opened) binders in the subcomp type
// subcomp_c: the computation type in the subcomp type (opened with bs)
// ct1 ct2: the two input computation types, both in M
// sub_prob: a function to create and add subproblems to the worklist
// wl: worklist
// subcomp_name and r1: for debugging purposes
//
// returns the (subcomp guard, new sub problems, worklist)
//
let apply_ad_hoc_indexed_subcomp (env:Env.env)
  (bs:binders)
  (subcomp_c:comp)
  (ct1:comp_typ) (ct2:comp_typ)
  (sub_prob:worklist -> term -> rel -> term -> string -> prob & worklist)
  (wl:worklist)
  (subcomp_name:string)
  (r1:Range.range)

  : typ & list prob & worklist =

  let stronger_t_shape_error s = BU.format2
    "Unexpected shape of stronger for %s, reason: %s"
      (Ident.string_of_lid ct2.effect_name) s in

  let a_b, rest_bs, f_b =
    if List.length bs >= 2
    then let a_b::bs = bs in
         let rest_bs, f_b =
           bs |> List.splitAt (List.length bs - 1)
              |> (fun (l1, l2) -> l1, List.hd l2) in
         a_b, rest_bs, f_b
    else raise_error r1 Errors.Fatal_UnexpectedExpressionType (stronger_t_shape_error "not an arrow or not enough binders") in

  let rest_bs_uvars, g_uvars =
    Env.uvars_for_binders env rest_bs
      [NT (a_b.binder_bv, ct2.result_typ)]
      (fun b ->
       if !dbg_LayeredEffectsApp
       then BU.format3 "implicit for binder %s in subcomp %s at %s"
              (show b)
              subcomp_name
              (Range.string_of_range r1)
       else "apply_ad_hoc_indexed_subcomp") r1 in

  let wl = { wl with wl_implicits = g_uvars.implicits ++ wl.wl_implicits } in

  let substs =
    List.map2 (fun b t -> NT (b.binder_bv, t))
              (a_b::rest_bs) (ct2.result_typ::rest_bs_uvars) in

  let f_sub_probs, wl =
    let f_sort_is =
      U.effect_indices_from_repr
        f_b.binder_bv.sort
        (Env.is_layered_effect env ct1.effect_name)
        r1 (stronger_t_shape_error "type of f is not a repr type")
      |> List.map (SS.subst substs) in

    List.fold_left2 (fun (ps, wl) f_sort_i c1_i ->
      if !dbg_LayeredEffectsApp
      then BU.print3 "Layered Effects (%s) %s = %s\n" subcomp_name
             (show f_sort_i) (show c1_i);
      let p, wl = sub_prob wl f_sort_i EQ c1_i "indices of c1" in
        ps@[p], wl
    ) ([], wl) f_sort_is (ct1.effect_args |> List.map fst) in

  let subcomp_ct = subcomp_c |> SS.subst_comp substs |> Env.comp_to_comp_typ env in

  let g_sub_probs, wl =
    let g_sort_is =
      U.effect_indices_from_repr
        subcomp_ct.result_typ
        (Env.is_layered_effect env ct2.effect_name)
        r1 (stronger_t_shape_error "subcomp return type is not a repr") in

    List.fold_left2 (fun (ps, wl) g_sort_i c2_i ->
      if !dbg_LayeredEffectsApp
      then BU.print3 "Layered Effects (%s) %s = %s\n" subcomp_name
             (show g_sort_i) (show c2_i);
      let p, wl = sub_prob wl g_sort_i EQ c2_i "indices of c2" in
      ps@[p], wl
    ) ([], wl) g_sort_is (ct2.effect_args |> List.map fst) in

  let fml =
    let u, wp = List.hd subcomp_ct.comp_univs, fst (List.hd subcomp_ct.effect_args) in
    Env.pure_precondition_for_trivial_post env u subcomp_ct.result_typ wp Range.dummyRange in

  fml,
  f_sub_probs@g_sub_probs,
  wl

let has_typeclass_constraint (u:ctx_uvar) (wl:worklist)
  : bool
  = wl.typeclass_variables |> for_any (fun v -> UF.equiv v.ctx_uvar_head u.ctx_uvar_head)

(* This function returns true for those lazykinds that
are "complete" in the sense that unfolding them does not
lose any information. For instance, embedded universes
are complete, since we embed them as applications of pack over a view,
and checking equality of such terms is equivalent to checking equality
of the views. Embedded proofstates are definitely not.

This is probably not the place for this function though. *)
let lazy_complete_repr (k:lazy_kind) : bool =
  match k with
  | Lazy_bv
  | Lazy_namedv
  | Lazy_binder
  | Lazy_letbinding
  | Lazy_fvar
  | Lazy_comp
  | Lazy_sigelt
  | Lazy_universe -> true
  | _ -> false

let has_free_uvars (t:term) : bool =
  not (Setlike.is_empty (Free.uvars_uncached t))

let env_has_free_uvars (e:env_t) : bool =
  List.existsb (fun b -> has_free_uvars b.binder_bv.sort) (Env.all_binders e)

let gamma_has_free_uvars (g:list binding) : bool =
  List.existsb (function Binding_var bv -> has_free_uvars bv.sort
                       | _ -> false) g

type reveal_hide_t =
  | Hide of (universe & typ & term)
  | Reveal of (universe & typ & term)

(******************************************************************************************************)
(* Main solving algorithm begins here *)
(******************************************************************************************************)
let rec solve (probs :worklist) : solution =
//    printfn "Solving TODO:\n%s;;" (List.map prob_to_string probs.attempting |> String.concat "\n\t");
    if !dbg_Rel
    then BU.print1 "solve:\n\t%s\n" (wl_to_string probs);
    if !dbg_ImplicitTrace then
      BU.print1 "solve: wl_implicits = %s\n" (show probs.wl_implicits);

    match next_prob probs with
    | Some (hd, tl, rank) ->
      let probs = {probs with attempting=tl} in
      def_check_prob "solve,hd" hd;
      begin match hd with
      | CProb cp ->
            solve_c (maybe_invert cp) probs

      | TProb tp ->
        if BU.physical_equality tp.lhs tp.rhs then solve (solve_prob hd None [] probs) else
        let is_expand_uvar (t:term) : bool =
          match (SS.compress t).n with
          | Tm_uvar (ctx_u, _) -> (UF.find_decoration ctx_u.ctx_uvar_head).uvar_decoration_should_unrefine
          | _ -> false
        in
        let maybe_expand (tp:tprob) : tprob =
          if Options.Ext.get "__unrefine" <> "" && tp.relation = SUB && is_expand_uvar tp.rhs
          then
            let lhs = tp.lhs in
            let lhs_norm = N.unfold_whnf' [Env.DontUnfoldAttr [PC.do_not_unrefine_attr]] (p_env probs hd) lhs in
            if Tm_refine? (SS.compress lhs_norm).n then
              (* It is indeed a refinement, normalize again to remove them. *)
              let lhs' = N.unfold_whnf' [Env.DontUnfoldAttr [PC.do_not_unrefine_attr]; Env.Unrefine] (p_env probs hd) lhs_norm in
              if !dbg_Rel then
                BU.print3 "GGG widening uvar %s! RHS %s ~> %s\n"
                  (show tp.rhs) (show lhs) (show lhs');
              { tp with lhs = lhs' }
            else
              tp
          else tp
        in

        let tp = maybe_expand tp in

        if rank=Rigid_rigid
        || (tp.relation = EQ && rank <> Flex_flex)
        then solve_t' tp probs
        else if probs.defer_ok = DeferAny
        then maybe_defer_to_user_tac tp "deferring flex_rigid or flex_flex subtyping" probs
        else if rank=Flex_flex
        then solve_t' ({tp with relation=EQ}) probs //turn flex_flex subtyping into flex_flex eq
        else solve_rigid_flex_or_flex_rigid_subtyping rank tp probs
      end

    | None ->
         begin
         match view probs.wl_deferred with
         | VNil ->
           Success (empty, as_deferred probs.wl_deferred_to_tac, probs.wl_implicits) //Yay ... done!

         | VCons _ _ ->
           let attempt, rest = probs.wl_deferred |> CList.partition (fun (c, _, _, _) -> c < probs.ctr) in
           match view attempt with
            | VNil -> //can't solve yet; defer the rest
              Success(as_deferred probs.wl_deferred,
                      as_deferred probs.wl_deferred_to_tac,
                      probs.wl_implicits)

            | _ ->
              solve ({probs with attempting=attempt |> to_list |> List.map (fun (_, _, _, y) -> y); wl_deferred=rest})
         end

and solve_one_universe_eq (orig:prob) (u1:universe) (u2:universe) (wl:worklist) : solution =
    match solve_universe_eq (p_pid orig) wl u1 u2 with
    | USolved wl ->
      solve (solve_prob orig None [] wl)

    | UFailed msg ->
      giveup wl msg orig

    | UDeferred wl ->
      solve (defer_lit Deferred_univ_constraint "" orig wl)

and solve_maybe_uinsts (orig:prob) (t1:term) (t2:term) (wl:worklist) : univ_eq_sol =
    let rec aux wl us1 us2 = match us1, us2 with
        | [], [] -> USolved wl

        | u1::us1, u2::us2 ->
          begin match solve_universe_eq (p_pid orig) wl u1 u2 with
            | USolved wl ->
              aux wl us1 us2

            | failed_or_deferred -> failed_or_deferred
          end

        | _ -> ufailed_simple "Unequal number of universes" in

    let env = p_env wl orig in
    def_check_scoped t1.pos "solve_maybe_uinsts.whnf1" env t1;
    def_check_scoped t2.pos "solve_maybe_uinsts.whnf2" env t2;
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

and giveup_or_defer (orig:prob) (wl:worklist) (reason:deferred_reason) (msg:lstring) : solution =
    if wl.defer_ok = DeferAny
    then begin
        if !dbg_Rel then
            BU.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" (prob_to_string wl.tcenv orig) (Thunk.force msg);
        solve (defer reason msg orig wl)
    end
    else giveup wl msg orig

and giveup_or_defer_flex_flex (orig:prob) (wl:worklist) (reason:deferred_reason) (msg:lstring) : solution =
    if wl.defer_ok <> NoDefer
    then begin
        if !dbg_Rel then
            BU.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" (prob_to_string wl.tcenv orig) (Thunk.force msg);
        solve (defer reason msg orig wl)
    end
    else giveup wl msg orig

and defer_to_user_tac (orig:prob) reason (wl:worklist) : solution =
  if !dbg_Rel then
    BU.print1 "\n\t\tDeferring %s to a tactic\n" (prob_to_string wl.tcenv orig);
  let wl = solve_prob orig None [] wl in
  let wl = {wl with wl_deferred_to_tac=cons (wl.ctr, Deferred_to_user_tac, Thunk.mkv reason, orig)  wl.wl_deferred_to_tac} in
  solve wl

and maybe_defer_to_user_tac prob reason wl : solution =
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
    then defer_to_user_tac (TProb prob) (r1 ^ ", " ^ r2) wl
    else solve (defer_lit Deferred_flex reason (TProb prob) wl)
  | _ -> solve (defer_lit Deferred_flex reason (TProb prob) wl)

(******************************************************************************************************)
(* The case where t1 < u, ..., tn < u: we solve this by taking u=t1\/...\/tn                          *)
(* The case where u < t1, .... u < tn: we solve this by taking u=t1/\.../\tn                          *)
(*                                                                                                    *)
(* This will go through the worklist to find problems for the same uvar u and compute the composite   *)
(* constraint as shown above.                                                                         *)
(******************************************************************************************************)
and solve_rigid_flex_or_flex_rigid_subtyping
    (rank:rank_t)
    (tp:tprob) (wl:worklist) : solution =
    def_check_prob "solve_rigid_flex_or_flex_rigid_subtyping" (TProb tp);
    let flip = rank = Flex_rigid in
    (* flip is true when the flex is on the left, after inverting (done by the caller),
       which means we have a problem of the shape ?u <: t

       if flip is false, we are solving something of shape t <: ?u *)
    (*
        meet_or_join op [t1;..;tn] env wl:
            Informally, this computes `t1 op t2 ... op tn`
            where op is either \/ or /\

            t1 op t2 is only defined when t1 and t2
            are refinements of the same base type

            if `op` is None, then we are computing the meet
            and the result is widened to the base type
    *)
    let meet_or_join 
           (op : option (term -> term -> term))
           (ts : list term)
           (wl:worklist)
      : term & list prob & worklist
      = let eq_prob t1 t2 wl =
            let p, wl =
            new_problem wl (p_env wl (TProb tp)) t1 EQ t2 None t1.pos
                        "join/meet refinements"
            in
            def_check_prob "meet_or_join" (TProb p);
            TProb p, wl
        in
        let pairwise t1 t2 wl =
            if !dbg_Rel
            then BU.print2 "[meet/join]: pairwise: %s and %s\n" (show t1) (show t2);
            let mr, ts = head_matches_delta (p_env wl (TProb tp)) tp.logical wl.smt_ok t1 t2 in
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
                  let wl' = {wl with defer_ok=NoDefer;
                                     smt_ok=false;
                                     attempting=probs;
                                     wl_deferred=empty;
                                     wl_implicits=empty} in
                  let tx = UF.new_transaction () in
                  match solve wl' with
                  | Success (_, defer_to_tac, imps) ->
                    UF.commit tx;
                    Some (extend_wl wl empty defer_to_tac imps)

                  | Failed _ ->
                    UF.rollback tx;
                    None
              in
              let combine (t1 t2 : term) wl : term & list prob & worklist =
                  let env = p_env wl (TProb tp) in
                  let t1_base, p1_opt = base_and_refinement_maybe_delta false env t1 in
                  let t2_base, p2_opt = base_and_refinement_maybe_delta false env t2 in
                  (*
                   * AR: before applying op, we need to squash phi if required
                   *     refinement formulas in F* may be in higher universe,
                   *       meaning that if we apply op (l_and or l_or) directly, we may be
                   *       unifying the universe of phi to zero, leading to errors
                   *)
                  let apply_op env op phi1 phi2 =
                    let squash phi =
                      match env.universe_of env phi with
                      | U_zero -> phi
                      | u -> U.mk_squash u phi in
                    op (squash phi1) (squash phi2)
                  in
                  let combine_refinements t_base p1_opt p2_opt =
                    match op with
                    | None -> t_base
                    | Some op ->
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
                        let env_x = Env.push_bv env x in
                        refine x (apply_op env_x op phi1 phi2)

                      | None, Some (x, phi)
                      | Some(x, phi), None ->
                        let x = freshen_bv x in
                        let subst = [DB(0, x)] in
                        let phi = SS.subst subst phi in
                        let env_x = Env.push_bv env x in
                        refine x (apply_op env_x op U.t_true phi)

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
              if !dbg_Rel
              then BU.print1 "pairwise fallback2 succeeded: %s"
                            (show t1);
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
    | Tm_arrow {bs=_bs; comp} ->
        //Although it's possible to take the meet/join of arrow types
        //we handle them separately either by imitation (for Tot/GTot arrows)
        //which provides some structural subtyping for them
        //or just by reducing it to equality in other cases

        //BEWARE: special treatment of Tot and GTot here
        if U.is_tot_or_gtot_comp comp
        then let flex, wl = destruct_flex_t this_flex wl in
             begin
             match quasi_pattern wl.tcenv flex with
             | None -> giveup_lit wl "flex-arrow subtyping, not a quasi pattern" (TProb tp)
             | Some (flex_bs, flex_t) ->
               if !dbg_Rel
               then BU.print1 "Trying to solve by imitating arrow:%s\n" (string_of_int tp.pid);
               imitate_arrow (TProb tp) wl flex flex_bs flex_t tp.relation this_rigid
             end
        else //imitating subtyping with WPs is hopeless
             solve (attempt [TProb ({tp with relation=EQ})] wl)

  | _ ->
    if !dbg_Rel then
      BU.print1 "Trying to solve by meeting refinements:%s\n" (show tp.pid);
    let u, _args = U.head_and_args this_flex in
    let env = p_env wl (TProb tp) in
    begin
    match (SS.compress u).n with
    | Tm_uvar(ctx_uvar, _subst) ->
      let equiv (t:term) : bool =
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
      begin
        let widen, meet_or_join_op = 
          if has_typeclass_constraint ctx_uvar wl
          && not flip //we are widening; so widen all the way
          then true, None
          else false, Some (if flip then U.mk_conj_simp else U.mk_disj_simp)
        in
        let (bound, sub_probs, wl) =
          match bounds_typs with
          | [t] ->
            if widen
            then fst (base_and_refinement_maybe_delta false env t), [], wl
            else (t, [], wl)
          | _ -> 
            meet_or_join meet_or_join_op
                        bounds_typs
                        wl
        in
        let bound_typ, (eq_prob, wl') =
            let flex_u = flex_uvar_head this_flex in
            let bound =
              //We get constraints of the form (x:?u{phi} <: ?u)
              //This cannot be solved with an equality constraints
              //So, turn the bound on the LHS to just ?u
              match (SS.compress bound).n with
              | Tm_refine {b=x; phi}
                when tp.relation=SUB
                  && snd (occurs flex_u x.sort) ->
                x.sort
              | _ ->
                bound
            in
            bound,
            new_problem wl (p_env wl (TProb tp)) bound EQ this_flex None tp.loc
                  (if flip then "joining refinements" else "meeting refinements")
        in
        def_check_prob "meet_or_join2" (TProb eq_prob);
        let _ = if !dbg_Rel
                then let wl' = {wl with attempting=TProb eq_prob::sub_probs} in
                    BU.print1 "After meet/join refinements: %s\n" (wl_to_string wl') in

        let tx = UF.new_transaction () in
        begin
        List.iter (def_check_prob "meet_or_join3_sub") sub_probs;
        match solve_t eq_prob ({wl' with defer_ok=NoDefer;
                                        wl_implicits = Listlike.empty;
                                        wl_deferred = empty;
                                        attempting=sub_probs}) with
        | Success (_, defer_to_tac, imps) ->
          let wl = {wl' with attempting=rest} in
          let wl = extend_wl wl empty defer_to_tac imps in
          let g =  List.fold_left (fun g p -> U.mk_conj g (p_guard p))
                                  eq_prob.logical_guard
                                  sub_probs in
          let wl = solve_prob' false (TProb tp) (Some g) [] wl in
          let _ = List.fold_left (fun wl p -> solve_prob' true p None [] wl) wl bounds_probs in
          UF.commit tx;
          solve wl

        | Failed (p, msg) ->
          if !dbg_Rel
          then BU.print1 "meet/join attempted and failed to solve problems:\n%s\n"
                          (List.map (prob_to_string env) (TProb eq_prob::sub_probs) |> String.concat "\n");
          (match rank, base_and_refinement env bound_typ with
            | Rigid_flex, (t_base, Some _) ->
              UF.rollback tx;
                //We failed to solve (x:t_base{p} <: ?u) while computing a precise join of all the lower bounds
                //Rather than giving up, try again with a widening heuristic
                //i.e., try to solve ?u = t and proceed
              let eq_prob, wl =
                  new_problem wl (p_env wl (TProb tp)) t_base EQ this_flex None tp.loc "widened subtyping" in
              def_check_prob "meet_or_join3" (TProb eq_prob);
              let wl = solve_prob' false (TProb tp) (Some (p_guard (TProb eq_prob))) [] wl in
              solve (attempt [TProb eq_prob] wl)

            | Flex_rigid, (t_base, Some (x, phi)) ->
              UF.rollback tx;
                //We failed to solve (?u = x:t_base{phi}) while computing
                //a precise meet of all the upper bounds
                //Rather than giving up, try again with a narrowing heuristic
                //i.e., solve ?u = t_base, with the guard formula phi
              let x = freshen_bv x in
              let _, phi = SS.open_term [S.mk_binder x] phi in
              let eq_prob, wl =
                  new_problem wl env t_base EQ this_flex None tp.loc "widened subtyping" in
              def_check_prob "meet_or_join4" (TProb eq_prob);
              let phi = guard_on_element wl tp x phi in
              let wl = solve_prob' false (TProb tp) (Some (U.mk_conj phi (p_guard (TProb eq_prob)))) [] wl in
              solve (attempt [TProb eq_prob] wl)

            | _ ->
              giveup wl (Thunk.map (fun s -> "failed to solve the sub-problems: " ^ s) msg) p)
        end
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

and imitate_arrow (orig:prob) (wl:worklist)
                  (lhs:flex_t) (bs_lhs:binders) (t_res_lhs:term)
                  (rel:rel)
                  (arrow:term)
        : solution =
        let bs_lhs_args = List.map (fun ({binder_bv=x;binder_qual=i}) -> S.bv_to_name x, i) bs_lhs in
        let (Flex (_, u_lhs, _)) = lhs in
        let imitate_comp bs bs_terms c wl =
           let imitate_tot_or_gtot t f wl =
              let k, _ = U.type_u () in
              let _, u, wl = copy_uvar u_lhs (bs_lhs@bs) k wl in
              f u, wl
           in
           match c.n with
           | Total t ->
             imitate_tot_or_gtot t S.mk_Total wl
           | GTotal t ->
             imitate_tot_or_gtot t S.mk_GTotal wl
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
        let rec aux (bs:binders) (bs_terms:list arg) (formals:binders) wl =
            match formals with
            | [] ->
              let c', wl = imitate_comp bs bs_terms c wl in
              let lhs' = U.arrow bs c' in
              let sol = TERM (u_lhs, U.abs bs_lhs lhs' (Some (U.residual_tot t_res_lhs))) in
              let sub_prob, wl =
                  mk_t_problem wl [] orig lhs' rel arrow None "arrow imitation"
              in
              //printfn "Arrow imitation: %s =?= %s" (show lhs') (show rhs);
              solve (attempt [sub_prob] (solve_prob orig None [sol] wl))

            | ({binder_bv=x;binder_qual=imp;binder_positivity=pqual;binder_attrs=attrs})::formals ->
              let _ctx_u_x, u_x, wl = copy_uvar u_lhs (bs_lhs@bs) (U.type_u() |> fst) wl in
              //printfn "Generated formal %s where %s" (show t_y) (show ctx_u_x);
              let y = S.new_bv (Some (S.range_of_bv x)) u_x in
              let b = S.mk_binder_with_attrs y imp pqual attrs in
              aux (bs@[b]) (bs_terms@[U.arg_of_non_null_binder b]) formals wl
         in
         let _, occurs_ok, msg = occurs_check u_lhs arrow in
         if not occurs_ok
         then giveup_or_defer orig wl
                Deferred_occur_check_failed
                (mklstr (fun () -> "occurs-check failed: " ^ (Option.get msg)))
         else aux [] [] formals wl

and solve_binders (bs1:binders) (bs2:binders) (orig:prob) (wl:worklist)
                  (rhs:worklist -> binders -> list subst_elt -> (prob & worklist)) : solution =

   if !dbg_Rel
   then BU.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                       (show bs1)
                       (rel_to_string (p_rel orig))
                       (show bs2);

   let eq_bqual a1 a2 =
       match a1, a2 with
       | Some (Implicit b1), Some (Implicit b2) ->
         true //we don't care about comparing the dot qualifier in this context
       | _ ->
         U.eq_bqual a1 a2
   in

   let compat_positivity_qualifiers (p1 p2:option positivity_qualifier) : bool =
      match p_rel orig with
      | EQ ->
        FStarC.TypeChecker.Common.check_positivity_qual false p1 p2
      | SUB ->
        FStarC.TypeChecker.Common.check_positivity_qual true p1 p2
      | SUBINV ->
        FStarC.TypeChecker.Common.check_positivity_qual true p2 p1
   in
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
   let rec aux wl scope subst (xs:binders) (ys:binders) : either (probs & formula) string & worklist =
        match xs, ys with
        | [], [] ->
          let rhs_prob, wl = rhs wl scope subst in
          if !dbg_Rel
          then BU.print1 "rhs_prob = %s\n" (prob_to_string (p_env wl rhs_prob) rhs_prob);
          let formula = p_guard rhs_prob in
          Inl ([rhs_prob], formula), wl

        | x::xs, y::ys 
          when (eq_bqual x.binder_qual y.binder_qual &&
                compat_positivity_qualifiers x.binder_positivity y.binder_positivity) ->
           let hd1, imp = x.binder_bv, x.binder_qual in
           let hd2, imp' = y.binder_bv, y.binder_qual in
           let hd1 = {hd1 with sort=Subst.subst subst hd1.sort} in //open both binders
           let hd2 = {hd2 with sort=Subst.subst subst hd2.sort} in
           let prob, wl = mk_t_problem wl scope orig hd1.sort (invert_rel <| p_rel orig) hd2.sort None "Formal parameter" in
           let hd1 = freshen_bv hd1 in
           let subst = DB(0, hd1)::SS.shift_subst 1 subst in  //extend the substitution
           begin
           match aux wl (scope @ [{x with binder_bv=hd1}]) subst xs ys with
           | Inl (sub_probs, phi), wl ->
             let phi =
                 U.mk_conj (p_guard prob)
                           (close_forall (p_env wl prob) [{x with binder_bv=hd1}] phi) in
             if !dbg_Rel
             then BU.print2 "Formula is %s\n\thd1=%s\n" (show phi) (show hd1);
             Inl (prob::sub_probs, phi), wl

           | fail -> fail
           end

        | _ -> Inr "arity or argument-qualifier mismatch", wl in

   match aux wl [] [] bs1 bs2 with
   | Inr msg, wl -> giveup_lit wl msg orig
   | Inl (sub_probs, phi), wl ->
     let wl = solve_prob orig (Some phi) [] wl in
     solve (attempt sub_probs wl)

and try_solve_without_smt_or_else
        (wl:worklist)
        (try_solve:  worklist -> solution)
        (else_solve: worklist -> (prob & lstring) -> solution)
    : solution =
    let wl' = {wl with defer_ok=NoDefer;
                       smt_ok=false;
                       umax_heuristic_ok=false;
                       attempting=[];
                       wl_deferred=empty;
                       wl_implicits=Listlike.empty} in
    let tx = UF.new_transaction () in
    match try_solve wl' with
    | Success (_, defer_to_tac, imps) ->
      UF.commit tx;
      let wl = extend_wl wl empty defer_to_tac imps in
      solve wl
    | Failed (p, s) ->
      UF.rollback tx;
      else_solve wl (p,s)

and try_solve_then_or_else
        (wl:worklist)
        (try_solve:  worklist -> solution)
        (then_solve: worklist -> solution)
        (else_solve: worklist -> solution)
    : solution =
    let empty_wl =
      {wl with defer_ok=NoDefer;
               attempting=[];
               wl_deferred=empty;
               wl_implicits=empty} in
    let tx = UF.new_transaction () in
    match try_solve empty_wl with
    | Success (_, defer_to_tac, imps) ->
      UF.commit tx;
      let wl = extend_wl wl empty defer_to_tac imps in
      then_solve wl
    | Failed (p, s) ->
      UF.rollback tx;
      else_solve wl

and try_solve_probs_without_smt
      (wl:worklist)
      (probs:worklist -> (probs & worklist))
  : either worklist lstring
  = let probs, wl' = probs wl in
    let wl' = {wl with defer_ok=NoDefer;
                       smt_ok=false;
                       umax_heuristic_ok=false;
                       attempting=probs;
                       wl_deferred=empty;
                       wl_implicits=Listlike.empty} in
    match solve wl' with
    | Success (_, defer_to_tac, imps) ->
      let wl = extend_wl wl empty defer_to_tac imps in
      Inl wl

    | Failed (_, ls) -> 
      Inr ls
      
and solve_t (problem:tprob) (wl:worklist) : solution =
    def_check_prob "solve_t" (TProb problem);
    solve_t' (compress_tprob wl problem) wl

and solve_t_flex_rigid_eq (orig:prob) (wl:worklist) (lhs:flex_t) (rhs:term)
    : solution =
    if !dbg_Rel then (
      BU.print1 "solve_t_flex_rigid_eq rhs=%s\n"
        (show rhs)
    );

    if should_defer_flex_to_user_tac wl lhs
    then defer_to_user_tac orig (flex_reason lhs) wl
    else

    (*
       mk_solution takes care to not introduce needless eta expansions

       lhs is of the form `?u bs`
       Abstractly, the goal is to set `?u := fun bs -> rhs`

       But, this is optimized so that in case `rhs` is say `e bs`,
       where `bs` does not appear free in `e`,
       then we set `?u := e`.

       This is important since eta equivalence is not validated by F*.

       So, introduce needless eta expansions here would lead to unification
       failures elsewhere
    *)
    let mk_solution env (lhs:flex_t) (bs:binders) (rhs:term) =
        let bs_orig = bs in
        let rhs_orig = rhs in
        let (Flex (_, ctx_u, args)) = lhs in
        let bs, rhs =
          let bv_not_free_in_arg x arg =
              not (mem x (Free.names (fst arg)))
          in
          let bv_not_free_in_args x args =
              BU.for_all (bv_not_free_in_arg x) args
          in
          let binder_matches_aqual b aq =
            match b.binder_qual, aq with
            | None, None -> true
            | Some (Implicit _), Some a ->
              a.aqual_implicit &&
              U.eqlist (fun x y -> TEQ.eq_tm env x y = TEQ.Equal)
                       b.binder_attrs
                       a.aqual_attributes
            | _ -> false
          in
          let rec remove_matching_prefix lhs_binders rhs_args =
            match lhs_binders, rhs_args with
            | [], _
            | _, [] -> lhs_binders, rhs_args

            | b::lhs_tl, (t, aq)::rhs_tl ->
              match (SS.compress t).n with
              | Tm_name x
                when bv_eq b.binder_bv x
                  && binder_matches_aqual b aq
                  && bv_not_free_in_args b.binder_bv rhs_tl ->
                remove_matching_prefix lhs_tl rhs_tl
              | _ ->
                lhs_binders, rhs_args
          in
          let rhs_hd, rhs_args = U.head_and_args rhs in
          let bs, rhs_args =
            remove_matching_prefix
              (List.rev bs_orig)
              (List.rev rhs_args)
            |> (fun (bs_rev, args_rev) -> List.rev bs_rev, List.rev args_rev)
          in
          bs,
          S.mk_Tm_app rhs_hd rhs_args rhs.pos
        in
        let sol =
          match bs with
          | [] -> rhs
          | _ -> u_abs (U.ctx_uvar_typ ctx_u) (sn_binders env bs) rhs
        in
        [TERM(ctx_u, sol)]
    in

    (*
      LHS: ?u e1..en, if the arity of ?u is n
           then LHS as a quasi pattern is (?u x1 ... xn)
           for some names x1...xn

           (see the comment on quasi_pattern on how these names are computed)


      if the free vars of rhs are included in ctx(?u) ++ {x1,...,xn}

      then solve by ?u <- (fun x1 .... xn -> rhs)

      provided ?u does not occur in RHS

      and after all uvars in the RHS (?u1 .. ?un) are restricted to the context (ctx(?u))

      This has the behavior of preserving functional dependences in *some* cases.

      Consider two examples:

      1.
          LHS = ?u A.x, where A.x is an fv
          RHS = option A.x

          Then quasi patern of LHS is (?u y), for some fresh y
          since we can't abstract over the A.x

          The resulting solution will be
            ?u <- fun y -> option A.x

          i.e., ?u is solved to the constant function
                rather than `option`

       2.  LHS = ?u x, where x is just a name DOES NOT APPEAR in ctx(?u)
           RHS = option (some complicated term including x)

           This time the quasi patern of LHS is (?u x) and
           the resulting solution will be

             ?u <- fun x -> option (some complicated term including x)

           preserving the dependence on `x`

    *)
    let try_quasi_pattern (orig:prob) (env:Env.env) (wl:worklist)
                          (lhs:flex_t) (rhs:term)
        : either string (list uvi) & worklist =
        if !dbg_Rel then
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
               if not (subset fvs_rhs fvs_lhs)
               then Inl ("quasi-pattern, free names on the RHS are not included in the LHS"), wl
               else Inr (mk_solution env lhs bs rhs), restrict_all_uvars env ctx_u [] uvars wl
    in

    (*
       LHS is a (?u e1..en) is a quasi pattern (?u b1...bn)
           where bs_lhs = b1 .. bn (none of which appear in ctx(?u) (see quasi_pattern))
           and the type of ?u is (b1..bn -> t_res_lhs)

       RHS is an application (head e)    where e:t_last

       Produce two new uvars:
          ctx(?u), b1..bn, _:t_last |- ?u_head : t_last -> t_res_lhs
          ctx(?u), b1..bn           |- ?u_arg  : t_last

       Solve: ?u <- (fun b1..bn -> ?u_head ?u_arg)

       And generate sub-problems
           ?u_head = head
           ?u_arg  = arg

       Since it is based on quasi patterns, imitate_app (like
       try_quasi_pattern) will usually not preserve functional
       dependences

       For example:

       1. LHS = ?u A.x, where A.x is an fv
          RHS = option A.x

          Then quasi patern of LHS is (?u y), for some fresh y
          since we can't abstract over the A.x

          The resulting solution will be

            ?u <- fun y -> ?u_head ?u_arg

            and ?u_head <- option
            and ?u_arg <- A.x

          So, in a more roundabout way, we arrive at the same constant
          function as the solution to ?u
    *)
    let imitate_app (orig:prob) (env:Env.env) (wl:worklist)
                    (lhs:flex_t) (bs_lhs:binders) (t_res_lhs:term)
                    (rhs:term)
        : solution =
        // if !dbg_Rel
        // then BU.print4 "imitate_app 1:\n\tlhs=%s\n\tbs_lhs=%s\n\tt_res_lhs=%s\n\trhs=%s\n"
        //    (flex_t_to_string lhs)
        //    (Print.binders_to_string ", " bs_lhs)
        //    (show t_res_lhs)
        //    (show rhs);
        let rhs_hd, args = U.head_and_args rhs in
        let args_rhs, last_arg_rhs = BU.prefix args in
        let rhs' = S.mk_Tm_app rhs_hd args_rhs rhs.pos in
        // if !dbg_Rel
        // then BU.print2 "imitate_app 2:\n\trhs'=%s\n\tlast_arg_rhs=%s\n"
        //            (show rhs')
        //            (show [last_arg_rhs]);
        let (Flex (t_lhs, u_lhs, _lhs_args)) = lhs in
        let lhs', lhs'_last_arg, wl =
              let t_last_arg, _ =
                let env = p_env wl orig in
                env.typeof_well_typed_tot_or_gtot_term
                  ({env with admit=true; expected_typ=None})
                  (fst last_arg_rhs)
                  false
              in  //AR: 03/30: WARNING: dropping the guard
              //AR: 07/20: note the type of lhs' is t_last_arg -> t_res_lhs
              let _, lhs', wl =
                let b = S.null_binder t_last_arg in
                copy_uvar u_lhs (bs_lhs@[b])
                (t_res_lhs |> S.mk_Total |> U.arrow [b]) wl
              in
              let _, lhs'_last_arg, wl = copy_uvar u_lhs bs_lhs t_last_arg wl in
              lhs', lhs'_last_arg, wl
        in
        // if !dbg_Rel
        // then BU.print2 "imitate_app 3:\n\tlhs'=%s\n\tlast_arg_lhs=%s\n"
        //            (show lhs')
        //            (show lhs'_last_arg);
        let sol = [TERM(u_lhs, U.abs bs_lhs (S.mk_Tm_app lhs' [(lhs'_last_arg, snd last_arg_rhs)] t_lhs.pos)
                                            (Some (U.residual_tot t_res_lhs)))]
        in
        let sub_probs, wl =
            let p1, wl = mk_t_problem wl [] orig lhs' EQ rhs' None "first-order lhs" in
            let p2, wl = mk_t_problem wl [] orig lhs'_last_arg EQ (fst last_arg_rhs) None "first-order rhs" in
            [p1; p2], wl
        in
        solve (attempt sub_probs (solve_prob orig None sol wl))
    in

    (*
       LHS: ?u e1..en, if the arity of ?u is n
            then LHS as a quasi pattern is (?u x1 ... xn)
            for some names x1...xn

            (see the comment on quasi_pattern on how these names are computed)

       If the RHS is an application (t e): imitate_app

       If the RHS is an arrow (xi:ti -> C): imitate_arrow
    *)
    let imitate (orig:prob) (env:Env.env) (wl:worklist)
                (lhs:flex_t) (rhs:term)
        : solution =
        if !dbg_Rel then
          BU.print_string "imitate\n";
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
                        BU.format1 "imitate heuristic cannot solve %s; lhs not a quasi-pattern"
                          (prob_to_string env orig)) in
           giveup_or_defer orig wl Deferred_first_order_heuristic_failed msg

        | Some (bs_lhs, t_res_lhs) ->
          if is_app rhs
          then imitate_app orig env wl lhs bs_lhs t_res_lhs rhs
          else if is_arrow rhs
          then imitate_arrow orig wl lhs bs_lhs t_res_lhs EQ rhs
          else
            let msg = mklstr (fun () ->
                                  BU.format1 "imitate heuristic cannot solve %s; rhs not an app or arrow"
                                  (prob_to_string env orig)) in
            giveup_or_defer orig wl Deferred_first_order_heuristic_failed msg
    in
    (*
          LHS = (?u : t1..tn -> t) e1..em
          RHS = f v1...vm

          if (f: t1..tn -> t)

             ?u <- f

          and generate (e1 =?= v1, ..., em =?= vm)
          
          while restricting all free uvars in f to the context of ?u
     *)
    let try_first_order orig env wl lhs rhs =
      let inapplicable msg lstring_opt =
         if !dbg_Rel
         then  (
           let extra_msg = 
             match lstring_opt with
             | None -> ""
             | Some l -> Thunk.force l
           in
           BU.print2 "try_first_order failed because: %s\n%s\n" msg extra_msg
         );
        Inl "first_order doesn't apply"
      in
      if !dbg_Rel then
          BU.print2 "try_first_order\n\tlhs=%s\n\trhs=%s\n"
                    (flex_t_to_string lhs)
                    (show rhs);
      let (Flex (_t1, ctx_uv, args_lhs)) = lhs in
      let n_args_lhs = List.length args_lhs in
      let head, args_rhs = U.head_and_args rhs in
      let n_args_rhs = List.length args_rhs in
      if n_args_lhs > n_args_rhs
      then inapplicable "not enough args" None
      else
        let i = n_args_rhs - n_args_lhs in
        let prefix, args_rhs = List.splitAt i args_rhs in
        let head = S.mk_Tm_app head prefix head.pos in
        let uvars_head, occurs_ok, _ = occurs_check ctx_uv head in
        if not occurs_ok
        then inapplicable "occurs check failed" None
        else if not (Free.names head `subset` binders_as_bv_set ctx_uv.ctx_uvar_binders)
        then inapplicable "free name inclusion failed" None
        else (
          let t_head, _ =
             env.typeof_well_typed_tot_or_gtot_term
                  ({env with admit=true; expected_typ=None})
                  head
                  false
          in
          let tx = UF.new_transaction () in
          let solve_sub_probs_if_head_types_equal head_uvars_to_restrict wl =
              let sol = [TERM(ctx_uv, head)] in
              let wl = restrict_all_uvars env ctx_uv [] head_uvars_to_restrict wl in
              let wl = solve_prob orig None sol wl in
              
              let sub_probs, wl =
                List.fold_left2
                  (fun (probs, wl) (arg_lhs, _) (arg_rhs, _) ->
                    let p, wl = mk_t_problem wl [] orig arg_lhs EQ arg_rhs None "first-order arg" in
                    p::probs, wl)
                  ([], wl)
                  args_lhs
                  args_rhs
              in
              let wl' = { wl  with defer_ok = NoDefer;
                                   smt_ok = false;
                                   attempting = sub_probs;
                                   wl_deferred = empty;
                                   wl_implicits = Listlike.empty } in
              match solve wl' with
              | Success (_, defer_to_tac, imps) ->
                let wl = extend_wl wl empty defer_to_tac imps in
                UF.commit tx;
                Inr wl
              | Failed (_, lstring) ->
                UF.rollback tx;
                inapplicable "Subprobs failed: " (Some lstring)
          in
          if TEQ.eq_tm env t_head (U.ctx_uvar_typ ctx_uv) = TEQ.Equal
          then
            //
            // eq_tm doesn't unify, so uvars_head computed remains consistent
            //   (see the second call to solve_sub_probs_if_head_types_equal below)
            //
            solve_sub_probs_if_head_types_equal uvars_head wl
          else (
              if !dbg_Rel
              then BU.print2  "first-order: head type mismatch:\n\tlhs=%s\n\trhs=%s\n"
                                              (show (U.ctx_uvar_typ ctx_uv))
                                              (show t_head);
              let typ_equality_prob wl =                                 
                let p, wl = mk_t_problem wl [] orig (U.ctx_uvar_typ ctx_uv) EQ t_head None "first-order head type" in
                [p], wl
              in
              match try_solve_probs_without_smt wl typ_equality_prob with
              | Inl wl ->
                //
                // Some uvars from uvars_head list above may already be solved
                //   or restricted, so recompute since solve_sub_probs_if_head_types_equal
                //   will also try to restrict them
                //
                solve_sub_probs_if_head_types_equal
                  (head |> Free.uvars |> elems)
                  wl
              | Inr msg ->
                UF.rollback tx;
                inapplicable "first-order: head type mismatch" (Some msg)
          )
      )
    in
    match p_rel orig with
    | SUB
    | SUBINV ->
      if wl.defer_ok = DeferAny
      then giveup_or_defer orig wl Deferred_flex (Thunk.mkv "flex-rigid subtyping")
      else solve_t_flex_rigid_eq (make_prob_eq orig) wl lhs rhs

    | EQ ->
      let (Flex (_t1, ctx_uv, args_lhs)) = lhs in
      let env = p_env wl orig in
      match pat_vars env ctx_uv.ctx_uvar_binders args_lhs with
      | Some lhs_binders -> //Pattern
        if !dbg_Rel then
          BU.print_string "it's a pattern\n";
        let rhs = sn env rhs in
        let fvs1 = binders_as_bv_set (ctx_uv.ctx_uvar_binders @ lhs_binders) in
        let fvs2 = Free.names rhs in
        //if !dbg_Rel then
        //  BU.print4 "lhs \t= %s\n\
        //             FV(lhs) \t= %s\n\
        //             rhs \t= %s\n\
        //             FV(rhs) \t= %s\n"
        //               (flex_t_to_string lhs)
        //               (show fvs1)
        //               (show rhs)
        //               (show fvs2);
        let uvars, occurs_ok, msg = occurs_check ctx_uv rhs in

        (* If the occurs check fails, attempt to do a bit more normalization
           and try it again. *)
        let (uvars, occurs_ok, msg), rhs =
          if occurs_ok
          then (uvars, occurs_ok, msg), rhs
          else
            let rhs = N.normalize
                          [Env.Primops; Env.Weak; Env.HNF; Env.Beta; Env.Eager_unfolding; Env.Unascribe]
                          (p_env wl orig) rhs in
            occurs_check ctx_uv rhs, rhs
        in

        (* If, possibly after some extra normalization in the above block,
        the RHS has become syntactically equal to the LHS, solve the problem
        and carry on. See #3264. *)
        if term_is_uvar ctx_uv rhs && Nil? args_lhs then
          solve (solve_prob orig None [] wl)
        else
        if not occurs_ok
        then giveup_or_defer orig wl
               Deferred_occur_check_failed
               (Thunk.mkv <| "occurs-check failed: " ^ (Option.get msg))
        else if subset fvs2 fvs1
        then let sol = mk_solution env lhs lhs_binders rhs in
             let wl = restrict_all_uvars env ctx_uv lhs_binders uvars wl in
             solve (solve_prob orig None sol wl)
        else if wl.defer_ok = DeferAny
        then
          let msg = mklstr (fun () ->
                                BU.format3 "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           (show fvs2)
                                           (show fvs1)
                                           (show (ctx_uv.ctx_uvar_binders @ lhs_binders))) in
          giveup_or_defer orig wl Deferred_free_names_check_failed msg
        else imitate orig env wl lhs rhs


      | _ -> //Not a pattern
        if wl.defer_ok = DeferAny
        then giveup_or_defer orig wl Deferred_not_a_pattern (Thunk.mkv "Not a pattern")
        else match try_first_order orig env wl lhs rhs with
             | Inr wl ->
                solve wl

             | _ ->

               match try_quasi_pattern orig env wl lhs rhs with
               | Inr sol, wl ->
                 solve (solve_prob orig None sol wl)

               | Inl msg, _ ->
                 imitate orig env wl lhs rhs

(* solve_t_flex-flex:
       Always delay flex-flex constraints, if possible.
       If not, see if one of the flex uvar has a meta program associated
               If yes, run that meta program, solve the uvar, and try again
               If not, coerce both sides to patterns and solve
*)
and solve_t_flex_flex env orig wl (lhs:flex_t) (rhs:flex_t) : solution =
    let should_run_meta_arg_tac (flex:flex_t) =
      (* If this flex has a meta-arg, and the problem is fully
      defined (no uvars in env/typ), then we can run it now. *)
      let uv = flex_uvar flex in
      flex_uvar_has_meta_tac uv &&
      not (has_free_uvars (U.ctx_uvar_typ uv)) &&
      not (gamma_has_free_uvars uv.ctx_uvar_gamma)
    in

    let run_meta_arg_tac_and_try_again (flex:flex_t) =
      let uv = flex_uvar flex in
      let t = run_meta_arg_tac env uv in
      if !dbg_Rel then
        BU.print2 "solve_t_flex_flex: solving meta arg uvar %s with %s\n" (show uv) (show t);
      set_uvar env uv None t;
      solve (attempt [orig] wl) in

    match p_rel orig with
    | SUB
    | SUBINV ->
      if wl.defer_ok = DeferAny
      then giveup_or_defer_flex_flex orig wl Deferred_flex (Thunk.mkv "flex-flex subtyping")
      else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs

    | EQ ->
      if should_defer_flex_to_user_tac wl lhs || should_defer_flex_to_user_tac wl rhs
      then defer_to_user_tac orig (flex_reason lhs ^", "^flex_reason rhs)wl
      else

      if (wl.defer_ok = DeferAny || wl.defer_ok = DeferFlexFlexOnly)
      && (not (is_flex_pat lhs)|| not (is_flex_pat rhs))
      then giveup_or_defer_flex_flex orig wl Deferred_flex_flex_nonpattern (Thunk.mkv "flex-flex non-pattern")

      else if should_run_meta_arg_tac lhs
      then run_meta_arg_tac_and_try_again lhs

      else if should_run_meta_arg_tac rhs
      then run_meta_arg_tac_and_try_again rhs

      else
          let rec occurs_bs u bs =
            match bs with
            | [] -> false
            | b::bs -> snd (occurs u b.binder_bv.sort) || occurs_bs u bs
          in
          match quasi_pattern env lhs, quasi_pattern env rhs with
          | Some (binders_lhs, t_res_lhs), Some (binders_rhs, t_res_rhs) ->
            let (Flex ({pos=range}, u_lhs, _)) = lhs in
            if occurs_bs u_lhs binders_lhs then
              (* Fix for #2583 *)
              giveup_or_defer orig wl Deferred_flex_flex_nonpattern
                (Thunk.mkv "flex-flex: occurs check failed on the LHS flex quasi-pattern")
            else
            let (Flex (_, u_rhs, _)) = rhs in
            if UF.equiv u_lhs.ctx_uvar_head u_rhs.ctx_uvar_head
            && binders_eq binders_lhs binders_rhs
            then solve (solve_prob orig None [] wl)
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
                 let new_uvar_typ = U.arrow zs (S.mk_Total t_res_lhs) in
                 if snd (occurs u_lhs new_uvar_typ)
                 ||  (not (Unionfind.equiv u_lhs.ctx_uvar_head u_rhs.ctx_uvar_head) &&
                     snd (occurs u_rhs new_uvar_typ))
                 then giveup_or_defer_flex_flex orig wl Deferred_flex_flex_nonpattern
                         (Thunk.mkv (BU.format1 "flex-flex: occurs\n defer_ok=%s\n"
                                                (show wl.defer_ok)))
                 else begin
                  //  let _ =
                  //    if !dbg_Rel
                  //    then BU.print1 "flex-flex quasi: %s\n"
                  //                   (BU.stack_dump())
                  //  in
                   let new_uvar_should_check, is_ghost =
                     match U.ctx_uvar_should_check u_lhs, U.ctx_uvar_should_check u_rhs with
                     | Allow_untyped r, Allow_untyped _ -> Allow_untyped r, false
                     | Allow_ghost r, _
                     | _, Allow_ghost r -> Allow_ghost r, true
                     | _ -> Strict, false in
                   let _, w, wl = new_uvar ("flex-flex quasi:"
                                           ^"\tlhs="  ^u_lhs.ctx_uvar_reason
                                           ^"\trhs=" ^u_rhs.ctx_uvar_reason)
                                         wl range gamma_w ctx_w new_uvar_typ
                                         new_uvar_should_check
                                         (if Some? u_lhs.ctx_uvar_meta
                                          then u_lhs.ctx_uvar_meta
                                          else u_rhs.ctx_uvar_meta) // Try to retain the meta, if any
                   in
                   let w_app = S.mk_Tm_app w (List.map (fun ({binder_bv=z}) -> S.as_arg (S.bv_to_name z)) zs) w.pos in
                   let _ =
                     if !dbg_Rel
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
                             show (ctx_l@binders_lhs);
                             show (ctx_r@binders_rhs);
                             show zs]
                   in
                   let rc = (if is_ghost then U.residual_gtot else U.residual_tot) t_res_lhs in
                   let s1_sol = U.abs binders_lhs w_app (Some rc) in
                   let s1 = TERM(u_lhs, s1_sol) in
                   if Unionfind.equiv u_lhs.ctx_uvar_head u_rhs.ctx_uvar_head
                   then solve (solve_prob orig None [s1] wl)
                   else (
                       let s2_sol = U.abs binders_rhs w_app (Some rc) in
                       let s2 = TERM(u_rhs, s2_sol) in
                       solve (solve_prob orig None [s1;s2] wl)
                     )
                 end

          | _ ->
            giveup_or_defer orig wl Deferred_flex_flex_nonpattern (Thunk.mkv "flex-flex: non-patterns")

and solve_t' (problem:tprob) (wl:worklist) : solution =
    def_check_prob "solve_t'.1" (TProb problem);
    let giveup_or_defer orig msg = giveup_or_defer orig wl msg in

    let rigid_heads_match (need_unif:bool) (torig:tprob) (wl:worklist) (t1:term) (t2:term) : solution =
        let orig = TProb torig in
        let env = p_env wl orig in
        if !dbg_Rel
        then BU.print5 "Heads %s: %s (%s) and %s (%s)\n"
            (if need_unif then "need unification" else "match")
            (show t1) (tag_of t1)
            (show t2) (tag_of t2);
        let head1, args1 = U.head_and_args t1 in
        let head2, args2 = U.head_and_args t2 in
        let need_unif =
          match (head1.n, args1), (head2.n, args2) with
          | (Tm_uinst(_, us1), _::_), (Tm_uinst(_, us2), _::_) ->
            if List.for_all (fun u -> not (universe_has_max env u)) us1
            && List.for_all (fun u -> not (universe_has_max env u)) us2
            then need_unif //if no umaxes then go ahead as usual
            else true //else, decompose the problem and potentially defer
          | _ -> need_unif
        in
        let solve_head_then wl k =
            if need_unif then k true wl
            else match solve_maybe_uinsts orig head1 head2 wl with
                 | USolved wl -> k true wl //(solve_prob orig None [] wl)
                 | UFailed msg -> giveup wl msg orig
                 | UDeferred wl -> k false (defer_lit Deferred_univ_constraint "universe constraints" orig wl)
        in
        let nargs = List.length args1 in
        if nargs <> List.length args2
        then giveup wl
                    (mklstr
                      (fun () -> BU.format4 "unequal number of arguments: %s[%s] and %s[%s]"
                                     (show head1) (show args1) (show head2) (show args2)))
                    orig
        else
        if nargs=0 || TEQ.eq_args env args1 args2=TEQ.Equal //special case: for easily proving things like nat <: nat, or greater_than i <: greater_than i etc.
        then if need_unif
             then solve_t ({problem with lhs=head1; rhs=head2}) wl
             else solve_head_then wl (fun ok wl ->
                    if ok then solve (solve_prob orig None [] wl)
                    else solve wl)
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
                   if !dbg_Rel
                   then BU.print2
                            "Adding subproblems for arguments (smtok=%s): %s"
                            (string_of_bool wl.smt_ok)
                            (FStarC.Common.string_of_list (prob_to_string env) subprobs);
                   if Options.defensive ()
                   then List.iter (def_check_prob "solve_t' subprobs") subprobs;
                   subprobs, wl
              in
              let solve_sub_probs env wl =
                  solve_head_then wl (fun ok wl ->
                      if not ok
                      then solve wl
                      else let subprobs, wl = mk_sub_probs wl in
                           let formula = U.mk_conj_l (List.map (fun p -> p_guard p) subprobs) in
                           let wl = solve_prob orig (Some formula) [] wl in
                           solve (attempt subprobs wl))
              in
              let solve_sub_probs_no_smt wl =
                  solve_head_then wl (fun ok wl ->
                      assert ok; //defer not allowed
                      let subprobs, wl = mk_sub_probs wl in
                      let formula = U.mk_conj_l (List.map (fun p -> p_guard p) subprobs) in
                      let wl = solve_prob orig (Some formula) [] wl in
                      solve (attempt subprobs wl))
              in
              let unfold_and_retry d wl (prob, reason) =
                   if !dbg_Rel
                   then BU.print2 "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                (prob_to_string env orig)
                                (Thunk.force reason);
                   let env = p_env wl prob in
                   match N.unfold_head_once env t1,
                         N.unfold_head_once env t2
                   with
                   | Some t1', Some t2' ->
                     let head1', _ = U.head_and_args t1' in
                     let head2', _ = U.head_and_args t2' in
                     begin
                     match TEQ.eq_tm env head1' head1, TEQ.eq_tm env head2' head2 with
                     | TEQ.Equal, TEQ.Equal -> //unfolding didn't make progress
                       if !dbg_Rel
                       then BU.print4
                            "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                (show t1)
                                (show t1')
                                (show t2)
                                (show t2');
                       solve_sub_probs env wl //fallback to trying to solve with SMT on
                     | _ ->
                       let torig' = {torig with lhs=t1'; rhs=t2'} in
                       if !dbg_Rel
                       then BU.print1 "Unfolded and now trying %s\n"
                                      (prob_to_string env (TProb torig'));
                       solve_t torig' wl
                     end
                   | _ ->
                     solve_sub_probs env wl //fallback to trying to solve with SMT on
              in
              let d = decr_delta_depth <| delta_depth_of_term env head1 in
              let treat_as_injective =
                match (U.un_uinst head1).n with
                | Tm_fvar fv ->
                  Env.fv_has_attr env fv PC.unifier_hint_injective_lid
                | _ -> false
              in
              begin
              match d with
              | Some d when wl.smt_ok && not treat_as_injective ->
                try_solve_without_smt_or_else wl
                    solve_sub_probs_no_smt
                    (unfold_and_retry d)

              | _ -> //cannot be unfolded or no smt anyway; so just try to solve extensionally
                solve_sub_probs env wl

              end

            | _ ->
              let lhs = force_refinement (base1, refinement1) in
              let rhs = force_refinement (base2, refinement2) in
              //
              //AR: force_refinement already returns the term in
              //    whnf, so call solve_t' directly
              //
              solve_t' ({problem with lhs=lhs; rhs=rhs}) wl
            end
    in

    (* <try_match_heuristic>:
          (match ?u with P1 -> t1 | ... | Pn -> tn) ~ t

          when (head t) `matches` (head ti)
          solve ?u to Pi
          and then try to prove `t ~ ti`
     *)
    let try_match_heuristic orig wl s1 s2 t1t2_opt =
        let env = p_env wl orig in
        let try_solve_branch scrutinee p =
            let (Flex (_t, uv, _args), wl) = destruct_flex_t scrutinee wl  in
            //
            // We add g_pat_as_exp implicits to the worklist later
            // And we know it only contains implicits, no logical payload
            //
            let xs, pat_term, g_pat_as_exp, _ = PatternUtils.pat_as_exp true true env p in
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

            //
            // The pat term here contains uvars for dot patterns, and even bvs
            //   and their types
            // We are going to unify the pat_term with the scrutinee, and that
            //   will solve some of those uvars
            // But there are some uvars, e.g. for the dot pattern types, that will
            //   not get constrained even with those unifications
            //
            // To constrain such uvars, we typecheck the pat_term with the type of
            //   the scrutinee as the expected type
            // This typechecking cannot use fastpath since the pat_term may be nested,
            //   and may have uvars in nested levels (Cons ?u (Cons ?u1 ...)),
            //   whereas fastpath may only compute the type from the top-level (list ?u here, e.g.)
            // And so on
            //

            let pat_term, g_pat_term =
              let must_tot = false in
              //
              // Note that we cannot just use the uv.ctx_uvar_typ,
              //   since _args may be non-empty
              // Also unrefine the scrutinee type
              //
              let scrutinee_t =
                env.typeof_well_typed_tot_or_gtot_term env scrutinee must_tot
                |> fst
                |> N.normalize_refinement N.whnf_steps env
                |> U.unrefine in
              if !dbg_Rel
              then BU.print1 "Match heuristic, typechecking the pattern term: %s {\n\n"
                     (show pat_term);
              let pat_term, pat_term_t, g_pat_term =
                env.typeof_tot_or_gtot_term
                  (Env.set_expected_typ env scrutinee_t)
                  pat_term
                  must_tot in
              if !dbg_Rel
              then BU.print2 "} Match heuristic, typechecked pattern term to %s and type %s\n"
                     (show pat_term)
                     (show pat_term_t);
              pat_term, g_pat_term in

            //
            // Enforce that the pattern typechecking guard has trivial logical payload
            //
            if g_pat_term |> simplify_guard env |> Env.is_trivial_guard_formula
            then begin
              let prob, wl = new_problem wl env scrutinee
                EQ pat_term None scrutinee.pos
                "match heuristic"
              in

              let wl' = extend_wl ({wl with defer_ok=NoDefer;
                                    smt_ok=false;
                                    attempting=[TProb prob];
                                    wl_deferred=empty;
                                    wl_implicits=Listlike.empty})
                                  g_pat_term.deferred
                                  g_pat_term.deferred_to_tac
                                  (Listlike.empty) in
              let tx = UF.new_transaction () in
              match solve wl' with
              | Success (_, defer_to_tac, imps) ->
                  let wl' = {wl' with attempting=[orig]} in
                  (match solve wl' with
                  | Success (_, defer_to_tac', imps') ->
                    UF.commit tx;
                    Some (extend_wl wl
                                    empty
                                    (defer_to_tac ++ defer_to_tac')
                                    (imps ++ imps' ++ g_pat_as_exp.implicits ++ g_pat_term.implicits))
  
                  | Failed _ ->
                    UF.rollback tx;
                    None)
              | _ ->
                UF.rollback tx;
                None
            end
            else None
        in
        match t1t2_opt with
        | None -> Inr None
        | Some (t1, t2) ->
            if !dbg_Rel
            then BU.print2 "Trying match heuristic for %s vs. %s\n"
                            (show t1)
                            (show t2);
            match (s1, U.unmeta t1), (s2, U.unmeta t2) with
            | (_, {n=Tm_match {scrutinee; brs=branches}}), (s, t)
            | (s, t), (_, {n=Tm_match {scrutinee; brs=branches}}) ->
              if not (is_flex scrutinee)
              then begin
                if !dbg_Rel
                then BU.print1 "match head %s is not a flex term\n" (show scrutinee);
                Inr None
              end
              else if wl.defer_ok = DeferAny
              then (if !dbg_Rel
                    then BU.print_string "Deferring ... \n";
                    Inl "defer")
              else begin
                  if !dbg_Rel
                  then BU.print2 "Heuristic applicable with scrutinee %s and other side = %s\n"
                                (show scrutinee)
                                (show t);
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
                              match head_matches_delta (p_env wl orig) (p_logical orig) wl.smt_ok s t' with
                              | FullMatch, _
                              | HeadMatch _, _ ->
                                true
                              | _ -> false
                            else false)
                  in
                  begin
                  match head_matching_branch with
                  | None ->
                    if !dbg_Rel
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
                    if !dbg_Rel
                    then BU.print2 "Found head matching branch %s -> %s\n"
                                (show p)
                                (show e);
                    Inr <| try_solve_branch scrutinee p

                  end
              end
            | _ ->
              if !dbg_Rel
              then BU.print2 "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                    (tag_of t1) (tag_of t2);
              Inr None
    in

    (* <rigid_rigid_delta>: are t1 and t2, with head symbols head1 and head2, compatible after some delta steps? *)
    let rigid_rigid_delta (torig:tprob) (wl:worklist)
                          (head1:term) (head2:term) (t1:term) (t2:term)
        : solution =
        let orig = TProb torig in
        if !dbg_RelDelta then
            BU.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                        (tag_of t1)
                        (tag_of t2)
                        (show t1)
                        (show t2);
        let m, o = head_matches_delta (p_env wl orig) (p_logical orig) wl.smt_ok t1 t2 in
        match m, o  with
        | (MisMatch _, _) -> //heads definitely do not match
            let try_reveal_hide t1 t2 =
                //tries to solve problems of the form
                // 1.
                // reveal ?u == y, where head y <> hide/reveal
                //   by generating hide (reveal ?u) == hide y
                //   and simplifying it to       ?u == hide y
                //
                // 2.
                //  hide ?u == y, where head y <> hide/reveal
                //  by generating reveal (hide ?u) == reveal y
                //  and simplifying it to       ?u == reveal y
                //
                let payload_of_hide_reveal h args : option (universe & typ & term) =
                    match h.n, args with
                    | Tm_uinst(_, [u]), [(ty, Some ({ aqual_implicit = true })); (t, _)] ->
                      Some (u, ty, t)
                    | _ -> None
                in
                let is_reveal_or_hide t =
                  let h, args = U.head_and_args t in
                  if U.is_fvar PC.reveal h
                  then match payload_of_hide_reveal h args with
                       | None -> None
                       | Some t -> Some (Reveal t)
                  else if U.is_fvar PC.hide h
                  then match payload_of_hide_reveal h args with
                       | None -> None
                       | Some t -> Some (Hide t)
                  else None
                in
                let mk_fv_app lid u args r =
                  let fv = Env.fvar_of_nonqual_lid wl.tcenv lid in
                  let head = S.mk_Tm_uinst fv [u]  in
                  S.mk_Tm_app head args r
                in
                match is_reveal_or_hide t1, is_reveal_or_hide t2 with
                (* We only apply these first two rules when the arg to reveal
                is a flex, to avoid loops such as:
                     reveal t1 =?= t2
                  ~> t1        =?= hide t2
                  ~> reveal t1 =?= t2
                *)
                | Some (Reveal (u, ty, lhs)), None when is_flex lhs ->
                  // reveal (?u _) / _
                  //add hide to rhs and simplify lhs
                  let rhs = mk_fv_app PC.hide u [(ty, S.as_aqual_implicit true); (t2, None)] t2.pos in
                  Some (lhs, rhs)

                | None, Some (Reveal (u, ty, rhs)) when is_flex rhs ->
                  // _ / reveal (?u _)
                  //add hide to lhs and simplify rhs
                  let lhs = mk_fv_app PC.hide u [(ty, S.as_aqual_implicit true); (t1, None)] t1.pos in
                  Some (lhs, rhs)

                | Some (Hide (u, ty, lhs)), None ->
                  // hide _ / _
                  //add reveal to rhs and simplify lhs
                  let rhs = mk_fv_app PC.reveal u [(ty,S.as_aqual_implicit true); (t2, None)] t2.pos in
                  Some (lhs, rhs)

                | None, Some (Hide (u, ty, rhs)) ->
                  // _ / hide _
                  //add reveal to lhs and simplify rhs
                  let lhs = mk_fv_app PC.reveal u [(ty,S.as_aqual_implicit true); (t1, None)] t1.pos in
                  Some (lhs, rhs)

                | _ -> None
            in
            begin
            match try_match_heuristic orig wl t1 t2 o with
            | Inl _defer_ok ->
              giveup_or_defer orig Deferred_delay_match_heuristic (Thunk.mkv "delaying match heuristic")

            | Inr (Some wl) ->
              solve wl

            | Inr None ->

              match try_reveal_hide t1 t2 with
              | Some (t1', t2') ->
                solve_t ({problem with lhs=t1'; rhs=t2'}) wl

              | None ->
                if (may_relate wl.tcenv problem.relation head1
                    || may_relate wl.tcenv problem.relation head2)
                && wl.smt_ok
                then let guard, wl = guard_of_prob wl problem t1 t2 in
                    solve (solve_prob orig (Some guard) [] wl)
                else giveup wl (mklstr (fun () -> BU.format4 "head mismatch (%s (%s) vs %s (%s))"
                                                  (show head1)
                                                  (show (delta_depth_of_term wl.tcenv head1))
                                                  (show head2)
                                                  (show (delta_depth_of_term wl.tcenv head2)))) orig
            end

        | (HeadMatch true, _) when problem.relation <> EQ ->
            //heads may only match after unification;
            //but we're not trying to unify them here
            //so, treat as a mismatch
            if wl.smt_ok
            then let guard, wl = guard_of_prob wl problem t1 t2 in
                    solve (solve_prob orig (Some guard) [] wl)
            else giveup wl (mklstr (fun () -> BU.format2 "head mismatch for subtyping (%s vs %s)"
                                        (show t1)
                                        (show t2)))
                                orig

        | (_, Some (t1, t2)) -> //heads match after some delta steps
            solve_t ({problem with lhs=t1; rhs=t2}) wl

        (* Need to maybe reunify the heads *)
        | (HeadMatch need_unif, None) ->
            rigid_heads_match need_unif torig wl t1 t2

        | (FullMatch, None) ->
            rigid_heads_match false torig wl t1 t2
    in
    (* <rigid_rigid_delta> *)

    let orig = TProb problem in
    def_check_prob "solve_t'.2" orig;
    if BU.physical_equality problem.lhs problem.rhs then solve (solve_prob orig None [] wl) else
    let t1 = problem.lhs in
    let t2 = problem.rhs in
    def_check_scoped (p_loc orig) "ref.t1" (List.map (fun b -> b.binder_bv) (p_scope orig)) t1;
    def_check_scoped (p_loc orig) "ref.t2" (List.map (fun b -> b.binder_bv) (p_scope orig)) t2;
    let _ =
        if !dbg_Rel
        then BU.print5 "Attempting %s (%s vs %s); rel = (%s); number of problems in wl = %s\n" (string_of_int problem.pid)
                            (tag_of t1 ^ "::" ^ show t1)
                            (tag_of t2 ^ "::" ^ show t2)
                            (rel_to_string problem.relation)
                            (show (List.length wl.attempting))
                            in
    match t1.n, t2.n with
      | Tm_delayed _, _
      | _, Tm_delayed _ ->
        // Either case is impossible since we always call solve_t' after
        // a call to compress_tprob, or directly after a call to unascribe,
        // unmeta, etc.
        failwith "Impossible: terms were not compressed"

      | Tm_ascribed _, _ ->
        solve_t' ({problem with lhs=U.unascribe t1}) wl

      | Tm_meta _, _ ->
        solve_t' ({problem with lhs=U.unmeta t1}) wl

      | _, Tm_ascribed _ ->
        solve_t' ({problem with rhs=U.unascribe t2}) wl

      | _, Tm_meta _ ->
        solve_t' ({problem with rhs=U.unmeta t2}) wl

      | Tm_quoted (t1, _), Tm_quoted (t2, _) ->
        solve (solve_prob orig None [] wl)

      | Tm_bvar _, _
      | _, Tm_bvar _ -> failwith "Only locally nameless! We should never see a de Bruijn variable"

      | Tm_type u1, Tm_type u2 ->
        solve_one_universe_eq orig u1 u2 wl

      | Tm_arrow {bs=bs1; comp=c1}, Tm_arrow {bs=bs2; comp=c2} ->
        let mk_c c = function
            | [] -> c
            | bs -> mk_Total(mk (Tm_arrow {bs; comp=c}) c.pos) in

        let (bs1, c1), (bs2, c2) =
            match_num_binders (bs1, mk_c c1) (bs2, mk_c c2) in

        solve_binders bs1 bs2 orig wl
        (fun wl scope subst  ->
            let c1 = Subst.subst_comp subst c1 in
            let c2 = Subst.subst_comp subst c2 in //open both comps
            let rel = if (Options.use_eq_at_higher_order()) then EQ else problem.relation in
            mk_c_problem wl scope orig c1 rel c2 None "function co-domain")

      | Tm_abs {bs=bs1; body=tbody1; rc_opt=lopt1},
        Tm_abs {bs=bs2; body=tbody2; rc_opt=lopt2} ->
        let mk_t t l = function
            | [] -> t
            | bs -> mk (Tm_abs {bs; body=t; rc_opt=l}) t.pos in
        let (bs1, tbody1), (bs2, tbody2) =
            match_num_binders (bs1, mk_t tbody1 lopt1) (bs2, mk_t tbody2 lopt2) in
        solve_binders bs1 bs2 orig wl
        (fun wl scope subst ->
           mk_t_problem wl scope orig (Subst.subst subst tbody1)
                                       problem.relation
                                       (Subst.subst subst tbody2) None "lambda co-domain")

      | Tm_refine {b=x1; phi=phi1}, Tm_refine {b=x2; phi=phi2} ->
        (* If the heads of their bases can match, make it so, and continue *)
        (* The unfolding is very much needed since we might have
         *   n:nat{phi n} =?= i:int{psi i}
         * and if we try to unify the bases, nat and int, we're toast.
         * However too much unfolding is also harmful for inference! See
         * the discussion on #1345. Hence we reuse head_matches_delta to
         * do the unfolding for us, which is good *heuristic* but not
         * necessarily always correct.
         *)
        let env = p_env wl (TProb problem) in
        let x1, x2 =
            match head_matches_delta env false wl.smt_ok x1.sort x2.sort with
            (* We allow (HeadMatch true) since we're gonna unify them again anyway via base_prob *)
            | FullMatch, Some (t1, t2)
            | HeadMatch _, Some (t1, t2) ->
                ({ x1 with sort = t1 }), ({ x2 with sort = t2 })
            | _ -> x1, x2
        in
        (* A bit hackish, reconstruct the refinements and flatten them with
        as_refinement. *)
        let t1 = S.mk (Tm_refine {b=x1; phi=phi1}) t1.pos in
        let t2 = S.mk (Tm_refine {b=x2; phi=phi2}) t2.pos in
        let x1, phi1 = as_refinement false env t1 in
        let x2, phi2 = as_refinement false env t2 in
        (* / hack *)
        if !dbg_Rel then begin
            BU.print3 "ref1 = (%s):(%s){%s}\n" (show x1)
                                               (show x1.sort)
                                               (show phi1);
            BU.print3 "ref2 = (%s):(%s){%s}\n" (show x2)
                                               (show x2.sort)
                                               (show phi2)
        end;
        let base_prob, wl = mk_t_problem wl [] orig x1.sort problem.relation x2.sort problem.element "refinement base type" in
        let x1 = freshen_bv x1 in
        let subst = [DB(0, x1)] in
        let phi1 = Subst.subst subst phi1 in
        let phi2 = Subst.subst subst phi2 in
        let mk_imp imp phi1 phi2 = imp phi1 phi2 |> guard_on_element wl problem x1 in
        let fallback () =
           let impl =
               if problem.relation = EQ
               then mk_imp U.mk_iff phi1 phi2
               else mk_imp U.mk_imp phi1 phi2 in
           let guard = U.mk_conj (p_guard base_prob) impl in
           def_check_scoped (p_loc orig) "ref.1" (List.map (fun b -> b.binder_bv) (p_scope orig)) (p_guard base_prob);
           def_check_scoped (p_loc orig) "ref.2" (List.map (fun b -> b.binder_bv) (p_scope orig)) impl;
           let wl = solve_prob orig (Some guard) [] wl in
           solve (attempt [base_prob] wl)
        in
        let has_uvars =
            not (Setlike.is_empty (FStarC.Syntax.Free.uvars phi1))
            || not (Setlike.is_empty (FStarC.Syntax.Free.uvars phi2))
        in
        if problem.relation = EQ
        || (not env.uvar_subtyping && has_uvars)
        then let ref_prob, wl =
                  mk_t_problem wl [mk_binder x1] orig phi1 EQ phi2 None "refinement formula"
             in
             let ref_prob = set_logical true ref_prob in
              
             let tx = UF.new_transaction () in
             (* We set wl_implicits to false, since in the success case we will
              * extend the original wl with the extra implicits we get, and we
              * do not want to duplicate the existing ones. *)
             match solve ({wl with defer_ok=NoDefer;
                                   wl_implicits=Listlike.empty;
                                   attempting=[ref_prob];
                                   wl_deferred=empty}) with
             | Failed (prob, msg) ->
               UF.rollback tx;
               if ((not env.uvar_subtyping && has_uvars)
                   || not wl.smt_ok)
                   && not env.unif_allow_ref_guards // if unif_allow_ref_guards is on, we don't give up
               then giveup wl msg prob
               else fallback()

             | Success (_, defer_to_tac, imps) ->
               UF.commit tx;
               let guard =
                   U.mk_conj (p_guard base_prob)
                             (p_guard ref_prob |> guard_on_element wl problem x1) in
               let wl = solve_prob orig (Some guard) [] wl in
               let wl = {wl with ctr=wl.ctr+1} in
               let wl = extend_wl wl empty defer_to_tac imps in
               solve (attempt [base_prob] wl)
        else fallback()

      (* flex-flex *)
      | Tm_uvar _,                Tm_uvar _
      | Tm_app {hd={n=Tm_uvar _}}, Tm_uvar _
      | Tm_uvar _,                Tm_app {hd={n=Tm_uvar _}}
      | Tm_app {hd={n=Tm_uvar _}}, Tm_app {hd={n=Tm_uvar _}} ->
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
        let env = p_env wl (TProb problem) in
        let t1, wl = ensure_no_uvar_subst env t1 wl in
        let t2 = U.canon_app t2 in
        (* ^ This canon_app call is needed for the incredibly infrequent case
         * where t2 is a Tm_app, its head uvar matches that of t1,
         * *and* the uvar is solved to an application by the previous
         * ensure_no_uvar_subst call. In that case, we get a nested application
         * in t2, and the call below would raise an error. *)
        let t2, wl = ensure_no_uvar_subst env t2 wl in
        let f1 = destruct_flex_t' t1 in
        let f2 = destruct_flex_t' t2 in
        solve_t_flex_flex env orig wl f1 f2

      (* flex-rigid equalities *)
      | Tm_uvar _, _
      | Tm_app {hd={n=Tm_uvar _}}, _ when (problem.relation=EQ) -> (* just imitate/project ... no slack *)
        let f1, wl = destruct_flex_t t1 wl in
        solve_t_flex_rigid_eq orig wl f1 t2

      (* rigid-flex: reorient if it is an equality constraint *)
      | _, Tm_uvar _
      | _, Tm_app {hd={n=Tm_uvar _}} when (problem.relation = EQ) ->
        solve_t' (invert problem) wl

      (* flex-rigid wrt an arrow: ?u _ <: t1 -> t2 *)
      | Tm_uvar _, Tm_arrow _
      | Tm_app {hd={n=Tm_uvar _}}, Tm_arrow _ ->
        //FIXME! This is weird; it should be handled by imitate_arrow
        //this case is so common, that even though we could delay, it is almost always ok to solve it immediately as an equality
        //besides, in the case of arrows, if we delay it, the arity of various terms built by the unifier goes awry
        //so, don't delay!
        solve_t' ({problem with relation=EQ}) wl

      | _, Tm_uvar _
      | _, Tm_app {hd={n=Tm_uvar _}}
      | Tm_uvar _, _
      | Tm_app {hd={n=Tm_uvar _}}, _ ->
        //flex-rigid subtyping is handled in the top-loop
        solve (attempt [TProb problem] wl)

      | Tm_abs _, _
      | _, Tm_abs _ ->
        let is_abs t = match t.n with
            | Tm_abs _ -> Inl t
            | _ -> Inr t in
        begin
            let env = p_env wl orig in
            match is_abs t1, is_abs t2 with
            | Inl t_abs, Inr not_abs
            | Inr not_abs, Inl t_abs ->
              if is_flex not_abs //if it's a pattern and the free var check succeeds, then unify it with the abstraction in one step
              && p_rel orig = EQ
              then let flex, wl = destruct_flex_t not_abs wl in
                    solve_t_flex_rigid_eq orig wl flex t_abs
              else begin
                match head_matches_delta env false wl.smt_ok not_abs t_abs with
                | HeadMatch _, Some (not_abs', _) ->
                  solve_t ({problem with lhs=not_abs'; rhs=t_abs}) wl

                | _ ->
                  let head, _ = U.head_and_args not_abs in
                  if wl.smt_ok
                  && may_relate wl.tcenv (p_rel orig) head
                  then let g, wl = mk_eq2 wl orig t_abs not_abs in
                       solve (solve_prob orig (Some g) [] wl)
                  else giveup wl (Thunk.mkv "head tag mismatch: RHS is an abstraction") orig
              end

            | _ -> failwith "Impossible: at least one side is an abstraction"
        end

      | Tm_refine _, _ ->
        let t2 = force_refinement <| base_and_refinement (p_env wl orig) t2 in
        solve_t' ({problem with rhs=t2}) wl

      | _, Tm_refine _ ->
        let t1 = force_refinement <| base_and_refinement (p_env wl orig) t1 in
        solve_t' ({problem with lhs=t1}) wl

      | Tm_match {scrutinee=s1;brs=brs1}, Tm_match {scrutinee=s2;brs=brs2} ->  //AR: note ignoring the return annotation
        let by_smt () =
            // using original WL
            let guard, wl = guard_of_prob wl problem t1 t2 in
            solve (solve_prob orig (Some guard) [] wl)
        in
        let rec solve_branches wl brs1 brs2 : option (list (binders & prob) & worklist) =
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
                if !dbg_Rel
                then BU.print2 "Created problem for branches %s with scope %s\n"
                                        (prob_to_string' wl prob)
                                        (show scope);
                BU.bind_opt (solve_branches wl rs1 rs2) (fun (r, wl) ->
                Some ((scope, prob)::(wprobs @ r), wl)))

            | [], [] -> Some ([], wl)
            | _ -> None
        in
        begin match solve_branches wl brs1 brs2 with
        | None ->
            if wl.smt_ok
            then by_smt ()
            else giveup wl (Thunk.mkv "Tm_match branches don't match") orig
        | Some (sub_probs, wl) ->
            let sc_prob, wl = mk_t_problem wl [] orig s1 EQ s2 None "match scrutinee" in
            let sub_probs = ([], sc_prob)::sub_probs in
            let formula = U.mk_conj_l (List.map (fun (scope, p) -> close_forall (p_env wl orig) scope (p_guard p)) sub_probs) in
            let tx = UF.new_transaction () in
            let wl = solve_prob orig (Some formula) [] wl in
            begin match solve (attempt (List.map snd sub_probs) ({wl with smt_ok = false})) with
            | Success (ds, ds', imp) ->
                UF.commit tx;
                Success (ds, ds', imp)
            | Failed _ ->
                UF.rollback tx;
                if wl.smt_ok
                then by_smt ()
                else giveup wl (Thunk.mkv "Could not unify matches without SMT") orig
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
             if !dbg_Rel
             then BU.print ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s; no_free_uvars=%s]\n"
               [(show problem.pid);
                (show wl.smt_ok);
                (show head1);
                (show (Env.is_interpreted wl.tcenv head1));
                (show (no_free_uvars t1));
                (show head2);
                (show (Env.is_interpreted wl.tcenv head2));
                (show (no_free_uvars t2))]
         in
         let equal t1 t2 : bool =
          (* Try comparing the terms as they are. If we get Equal or NotEqual,
             we are done. If we get an Unknown, attempt some normalization. *)
           let env = p_env wl orig in
           let r = TEQ.eq_tm env t1 t2 in
           match r with
           | TEQ.Equal -> true
           | TEQ.NotEqual -> false
           | TEQ.Unknown ->
             let steps = [
               Env.UnfoldUntil delta_constant;
               Env.Primops;
               Env.Beta;
               Env.Eager_unfolding;
               Env.Iota ] in
             let t1 = norm_with_steps "FStarC.TypeChecker.Rel.norm_with_steps.2" steps env t1 in
             let t2 = norm_with_steps "FStarC.TypeChecker.Rel.norm_with_steps.3" steps env t2 in
             TEQ.eq_tm env t1 t2 = TEQ.Equal
         in
         if (Env.is_interpreted wl.tcenv head1 || Env.is_interpreted wl.tcenv head2) //we have something like (+ x1 x2) =?= (- y1 y2)
           && problem.relation = EQ
         then (
           let solve_with_smt () =
             let guard, wl =
                 if equal t1 t2
                 then None, wl
                 else let g, wl = mk_eq2 wl orig t1 t2 in
                      Some g, wl
             in
             solve (solve_prob orig guard [] wl)
           in
           if no_free_uvars t1 // and neither term has any free variables
           && no_free_uvars t2
           then
             if not wl.smt_ok
             || Options.ml_ish ()
             then if equal t1 t2
                  then solve (solve_prob orig None [] wl)
                  else rigid_rigid_delta problem wl head1 head2 t1 t2
             else solve_with_smt()
           else if not wl.smt_ok
                || Options.ml_ish()
           then rigid_rigid_delta problem wl head1 head2 t1 t2
           else (
            try_solve_then_or_else
              wl
              (*try*)
              (fun wl_empty -> rigid_rigid_delta problem wl_empty head1 head2 t1 t2)
              (*then*)
              (fun wl -> solve wl)
              (*else*)
              (fun _ -> solve_with_smt())
            )
         )
         else (
             rigid_rigid_delta problem wl head1 head2 t1 t2
         )


      | Tm_let _, Tm_let _ ->
         // For now, just unify if they syntactically match
         if U.term_eq t1 t2
         then solve (solve_prob orig None [] wl)
         else giveup wl (Thunk.mkv "Tm_let mismatch") orig

      | Tm_let _, _
      | _, Tm_let _ ->
         raise_error t1 Errors.Fatal_UnificationNotWellFormed
           (BU.format4 "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                            (tag_of t1) (tag_of t2) (show t1) (show t2))

      | Tm_lazy li1, Tm_lazy li2 when li1.lkind =? li2.lkind
                                   && lazy_complete_repr li1.lkind ->
        solve_t' ({problem with lhs = U.unfold_lazy li1; rhs = U.unfold_lazy li2}) wl

      | _ -> giveup wl (Thunk.mk (fun () -> "head tag mismatch: " ^ tag_of t1 ^ " vs " ^ tag_of t2)) orig

and solve_c (problem:problem comp) (wl:worklist) : solution =
    let c1 = problem.lhs in
    let c2 = problem.rhs in
    let orig = CProb problem in
    let env = p_env wl orig in
    let sub_prob : worklist -> term -> rel -> term -> string -> prob & worklist =
        fun wl t1 rel t2 reason -> mk_t_problem wl [] orig t1 rel t2 None reason in

    let solve_eq c1_comp c2_comp g_lift =
        let _ = if !dbg_EQ
                then BU.print2 "solve_c is using an equality constraint (%s vs %s)\n"
                            (show (mk_Comp c1_comp))
                            (show (mk_Comp c2_comp)) in
        if not (lid_equals c1_comp.effect_name c2_comp.effect_name)
        then giveup wl (mklstr (fun () -> BU.format2 "incompatible effects: %s <> %s"
                                        (show c1_comp.effect_name)
                                        (show c2_comp.effect_name))) orig
        else if List.length c1_comp.effect_args <> List.length c2_comp.effect_args
        then giveup wl (mklstr (fun () -> BU.format2 "incompatible effect arguments: %s <> %s"
                                        (show c1_comp.effect_args)
                                        (show c2_comp.effect_args))) orig
        else
             let univ_sub_probs, wl =
               List.fold_left2 (fun (univ_sub_probs, wl) u1 u2 ->
                 let p, wl = sub_prob wl
                   (S.mk (S.Tm_type u1) Range.dummyRange)
                   EQ
                   (S.mk (S.Tm_type u2) Range.dummyRange)
                   "effect universes" in
                 (univ_sub_probs ++ cons p empty), wl) (empty, wl) c1_comp.comp_univs c2_comp.comp_univs in
             let ret_sub_prob, wl = sub_prob wl c1_comp.result_typ EQ c2_comp.result_typ "effect ret type" in
             let arg_sub_probs, wl =
                 List.fold_right2
                        (fun (a1, _) (a2, _) (arg_sub_probs, wl) ->
                           let p, wl = sub_prob wl a1 EQ a2 "effect arg" in
                           cons p arg_sub_probs, wl)
                        c1_comp.effect_args
                        c2_comp.effect_args
                        (empty, wl)
             in
             let sub_probs : clist _ =
               univ_sub_probs ++
               (cons ret_sub_prob <|
                arg_sub_probs ++
                (g_lift.deferred |> CList.map (fun (_, _, p) -> p)))
             in
             let sub_probs : list _ = to_list sub_probs in
             let guard =
               let guard = U.mk_conj_l (List.map p_guard sub_probs) in
               match g_lift.guard_f with
               | Trivial -> guard
               | NonTrivial f -> U.mk_conj guard f in
             let wl = { wl with wl_implicits = g_lift.implicits ++ wl.wl_implicits } in
             let wl = solve_prob orig (Some guard) [] wl in
             solve (attempt sub_probs wl)
    in

    let should_fail_since_repr_subcomp_not_allowed
      (repr_subcomp_allowed:bool)
      (c1 c2:lid) : bool
      = let c1, c2 = Env.norm_eff_name wl.tcenv c1, Env.norm_eff_name wl.tcenv c2 in
        not wl.repr_subcomp_allowed
        && not (lid_equals c1 c2)
        && Env.is_reifiable_effect wl.tcenv c2 in
                  // GM: What I would like to write instead of these two
                  // last conjuncts is something like
                  // [Option.isSome edge.mlift.mlift_term],
                  // but it seems that we always carry around a Some
                  // (fun _ _ e -> e) instead of a None even for
                  // primitive effects.

    let solve_layered_sub c1 c2 =
      if !dbg_LayeredEffectsApp then
        BU.print2 "solve_layered_sub c1: %s and c2: %s {\n"
          (c1 |> S.mk_Comp |> show)
          (c2 |> S.mk_Comp |> show);

      if problem.relation = EQ
      then solve_eq c1 c2 Env.trivial_guard
      else
        let r = Env.get_range wl.tcenv in

        if should_fail_since_repr_subcomp_not_allowed
             wl.repr_subcomp_allowed
             c1.effect_name
             c2.effect_name
        then giveup wl (mklstr (fun () -> BU.format2 "Cannot lift from %s to %s, it needs a lift\n"
                                            (string_of_lid c1.effect_name)
                                            (string_of_lid c2.effect_name)))
                    orig
        else
          let subcomp_name = BU.format2 "%s <: %s"
            (c1.effect_name |> Ident.ident_of_lid |> Ident.string_of_id)
            (c2.effect_name |> Ident.ident_of_lid |> Ident.string_of_id) in

          let lift_c1 (edge:edge) : comp_typ & guard_t =
            c1 |> S.mk_Comp |> edge.mlift.mlift_wp env
               |> (fun (c, g) -> Env.comp_to_comp_typ env c, g) in
  
          let c1, g_lift, stronger_t_opt, kind, num_eff_params, is_polymonadic =
            match Env.exists_polymonadic_subcomp env c1.effect_name c2.effect_name with
            | None ->
              // there is no polymonadic bind c1 <: c2
              // see if c1 can be lifted to c2
              (match Env.monad_leq env c1.effect_name c2.effect_name with
               | None ->
                 // c1 cannot be lifted to c2, fail
                 //   (sets stronger_t_opt to None)
                 //
                 c1, Env.trivial_guard, None, Ad_hoc_combinator, 0, false
               | Some edge ->
                 // there is a way to lift c1 to c2 via edge
                 let c1, g_lift = lift_c1 edge in
                 let ed2 = c2.effect_name |> Env.get_effect_decl env in
                 let tsopt, k = ed2
                   |> U.get_stronger_vc_combinator
                   |> (fun (ts, kopt) -> Env.inst_tscheme_with ts c2.comp_univs |> snd |> Some, kopt |> must) in
                 let num_eff_params =
                   match ed2.signature with
                   | Layered_eff_sig (n, _) -> n
                   | _ -> failwith "Impossible (expected indexed effect subcomp)" in
                 c1, g_lift, tsopt, k, num_eff_params, false)
            | Some (t, kind) ->
              c1, Env.trivial_guard,
              Env.inst_tscheme_with t c2.comp_univs |> snd |> Some,
              kind,
              0,
              true in

          if is_none stronger_t_opt
          then giveup wl (mklstr (fun () -> BU.format2 "incompatible monad ordering: %s </: %s"
                                          (show c1.effect_name)
                                          (show c2.effect_name))) orig
          else
            let stronger_t = stronger_t_opt |> must in
            // we will account for g_lift logical guard later
            let wl = extend_wl wl g_lift.deferred g_lift.deferred_to_tac g_lift.implicits in

            if is_polymonadic &&
               Env.is_erasable_effect env c1.effect_name &&
               not (Env.is_erasable_effect env c2.effect_name) &&
               not (N.non_info_norm env c1.result_typ)
            then Errors.raise_error r Errors.Error_TypeError
                                     (BU.format3 "Cannot lift erasable expression from %s ~> %s since its type %s is informative"
                                       (string_of_lid c1.effect_name)
                                       (string_of_lid c2.effect_name)
                                       (show c1.result_typ));

            (*
             * AR: 04/08: Suppose we have a subcomp problem of the form:
             *            M a ?u <: M a wp or M a wp <: M a ?u
             *
             *            If we simply applied the stronger (subcomp) combinator,
             *              there is a chance that the uvar would escape into the
             *              refinements/wp and remain unresolved
             *
             *            So, if this is the case (i.e. an effect index on one side is a uvar)
             *              we solve this particular index with equality ?u = wp
             *
             *            There are two exceptions:
             *              If it is a polymonadic subcomp (the indices may not be   symmetric)
             *              If uvar is to be solved using a user-defined tactic
             *
             * TODO: apply this equality heuristic to non-layered effects also
             *)

            //sub problems for uvar indices in c1
            let is_sub_probs, wl =
              if is_polymonadic then [], wl
              else
                let rec is_uvar t =  //t is a uvar that is not to be solved by a user tactic
                  match (SS.compress t).n with
                  | Tm_uvar (uv, _) ->
                    not (DeferredImplicits.should_defer_uvar_to_user_tac env uv)
                  | Tm_uinst (t, _) -> is_uvar t
                  | Tm_app {hd=t} -> is_uvar t
                  | _ -> false in
                List.fold_right2 (fun (a1, _) (a2, _) (is_sub_probs, wl) ->
                  if is_uvar a1
                  then begin
                         if !dbg_LayeredEffectsEqns then
                         BU.print2 "Layered Effects teq (rel c1 index uvar) %s = %s\n"
                           (show a1) (show a2);
                         let p, wl = sub_prob wl a1 EQ a2 "l.h.s. effect index uvar" in
                         p::is_sub_probs, wl
                       end
                   else is_sub_probs, wl
                ) c1.effect_args c2.effect_args ([], wl) in

            //return type sub problem
            let ret_sub_prob, wl = sub_prob wl c1.result_typ problem.relation c2.result_typ "result type" in

            let bs, subcomp_c = U.arrow_formals_comp stronger_t in

            let fml, sub_probs, wl =
              if kind = Ad_hoc_combinator
              then apply_ad_hoc_indexed_subcomp env bs subcomp_c c1 c2 sub_prob wl subcomp_name r
              else apply_substitutive_indexed_subcomp env kind bs subcomp_c c1 c2 sub_prob
                   num_eff_params
                   wl
                   subcomp_name r in

            let sub_probs = ret_sub_prob::(is_sub_probs@sub_probs) in

            let guard =
              let guard = U.mk_conj_l (List.map p_guard sub_probs) in
              let guard =
                match g_lift.guard_f with
                | Trivial -> guard
                | NonTrivial f -> U.mk_conj guard f in
              U.mk_conj guard fml in

            let wl = solve_prob orig (Some guard) [] wl in
            if !dbg_LayeredEffectsApp
            then  BU.print_string "}\n";
            solve (attempt sub_probs wl) in

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
                 then raise_error r Errors.Fatal_UnexpectedEffect
                        (BU.format2 "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                          (show c1.effect_name) (show c2.effect_name))
                 else Env.comp_to_comp_typ env c)
        in
        if should_fail_since_repr_subcomp_not_allowed
             wl.repr_subcomp_allowed
             c1.effect_name
             c2.effect_name
        then giveup wl (mklstr (fun () -> BU.format2 "Cannot lift from %s to %s, it needs a lift\n"
                                            (string_of_lid c1.effect_name)
                                            (string_of_lid c2.effect_name)))
                        orig
        else let is_null_wp_2 = c2.flags |> BU.for_some (function TOTAL | MLEFFECT | SOMETRIVIAL -> true | _ -> false) in
             let wpc1, wpc2 = match c1.effect_args, c2.effect_args with
              | (wp1, _)::_, (wp2, _)::_ -> wp1, wp2
              | _ ->
                raise_error env Errors.Fatal_ExpectNormalizedEffect
                  (BU.format2 "Got effects %s and %s, expected normalized effects" (show c1.effect_name) (show c2.effect_name))
             in

             if BU.physical_equality wpc1 wpc2
             then solve_t (problem_using_guard orig c1.result_typ problem.relation c2.result_typ None "result type") wl
             else let c2_decl, qualifiers = must (Env.effect_decl_opt env c2.effect_name) in
                  if qualifiers |> List.contains Reifiable
                  then let c1_repr =
                           norm_with_steps "FStarC.TypeChecker.Rel.norm_with_steps.4"
                                           [Env.UnfoldUntil delta_constant; Env.Weak; Env.HNF] env
                                           (Env.reify_comp env (S.mk_Comp (lift_c1 ())) (env.universe_of env c1.result_typ))
                       in
                       let c2_repr =
                           norm_with_steps "FStarC.TypeChecker.Rel.norm_with_steps.5"
                                           [Env.UnfoldUntil delta_constant; Env.Weak; Env.HNF] env
                                           (Env.reify_comp env (S.mk_Comp c2) (env.universe_of env c2.result_typ))
                       in
                       let prob, wl =
                           sub_prob wl c1_repr problem.relation c2_repr
                                    (BU.format2 "sub effect repr: %s <: %s"
                                                    (show c1_repr)
                                                    (show c2_repr))
                       in
                       let wl = solve_prob orig (Some (p_guard prob)) [] wl in
                       solve (attempt [prob] wl)
                  else
                      let g =
                         if Options.lax () then
                            U.t_true
                         else let wpc1_2 = lift_c1 () |> (fun ct -> List.hd ct.effect_args) in
                              if is_null_wp_2
                              then let _ = if !dbg_Rel
                                           then BU.print_string "Using trivial wp ... \n" in
                                   let c1_univ = env.universe_of env c1.result_typ in
                                   let trivial =
                                     match c2_decl |> U.get_wp_trivial_combinator with
                                     | None -> failwith "Rel doesn't yet handle undefined trivial combinator in an effect"
                                     | Some t -> t in
                                   mk (Tm_app {hd=inst_effect_fun_with [c1_univ] env c2_decl trivial;
                                               args=[as_arg c1.result_typ; wpc1_2]}) r
                              else let c2_univ = env.universe_of env c2.result_typ in
                                   let stronger = c2_decl |> U.get_stronger_vc_combinator |> fst in
                                   mk (Tm_app {hd=inst_effect_fun_with [c2_univ] env c2_decl stronger;
                                               args=[as_arg c2.result_typ; as_arg wpc2; wpc1_2]}) r in
                      if !dbg_Rel then
                          BU.print1 "WP guard (simplifed) is (%s)\n" (show (N.normalize [Env.Iota; Env.Eager_unfolding; Env.Primops; Env.Simplify] env g));
                      let base_prob, wl = sub_prob wl c1.result_typ problem.relation c2.result_typ "result type" in
                      let wl = solve_prob orig (Some <| U.mk_conj (p_guard base_prob) g) [] wl in
                      solve (attempt [base_prob] wl)
    in

    if BU.physical_equality c1 c2
    then solve (solve_prob orig None [] wl)
    else let _ = if !dbg_Rel
                 then BU.print3 "solve_c %s %s %s\n"
                                    (show c1)
                                    (rel_to_string problem.relation)
                                    (show c2) in

         //AR: 10/18: try ghost to pure promotion only if effects are different

         let c1, c2 =
           let eff1, eff2 =
             c1 |> U.comp_effect_name |> Env.norm_eff_name env,
             c2 |> U.comp_effect_name |> Env.norm_eff_name env in
           if Ident.lid_equals eff1 eff2
           then c1, c2
           else N.ghost_to_pure2 env (c1, c2) in

         match c1.n, c2.n with
         | GTotal t1, Total t2 when (Env.non_informative env t2) ->
           solve_t (problem_using_guard orig t1 problem.relation t2 None "result type") wl

         | GTotal _, Total _ ->
           giveup wl (Thunk.mkv "incompatible monad ordering: GTot </: Tot")  orig

         | Total  t1, Total  t2
         | GTotal t1, GTotal t2 -> //rigid-rigid 1
           solve_t (problem_using_guard orig t1 problem.relation t2 None "result type") wl

         | Total  t1, GTotal t2 when problem.relation = SUB ->
           solve_t (problem_using_guard orig t1 problem.relation t2 None "result type") wl

         | Total  t1, GTotal t2 ->
           giveup wl (Thunk.mkv "GTot =/= Tot") orig

         | GTotal _, Comp _
         | Total _,  Comp _ ->
           solve_c ({problem with lhs=mk_Comp <| Env.comp_to_comp_typ env c1}) wl

         | Comp _, GTotal _
         | Comp _, Total _ ->
           solve_c ({problem with rhs=mk_Comp <| Env.comp_to_comp_typ env c2}) wl

         | Comp _, Comp _ ->
            if (U.is_ml_comp c1 && U.is_ml_comp c2)
            || (U.is_total_comp c1 && U.is_total_comp c2)
            || (U.is_total_comp c1 && U.is_ml_comp c2 && problem.relation=SUB)
            then solve_t (problem_using_guard orig (U.comp_result c1) problem.relation (U.comp_result c2) None "result type") wl
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
                    if !dbg_Rel then BU.print2 "solve_c for %s and %s\n" (string_of_lid c1.effect_name) (string_of_lid c2.effect_name);
                    if Env.is_layered_effect env c2.effect_name then solve_layered_sub c1 c2
                    else
                      match Env.monad_leq env c1.effect_name c2.effect_name with
                      | None ->
                       giveup wl (mklstr (fun () -> BU.format2 "incompatible monad ordering: %s </: %s"
                                              (show c1.effect_name)
                                              (show c2.effect_name))) orig
                      | Some edge ->
                        solve_sub c1 edge c2
                 end

(* -------------------------------------------------------- *)
(* top-level interface                                      *)
(* -------------------------------------------------------- *)
let print_pending_implicits g =
    g.implicits |> CList.map (fun i -> show i.imp_uvar) |> show

let ineqs_to_string (ineqs : clist universe & clist (universe & universe)) =
    let (vars, ineqs) = ineqs in
    let ineqs = ineqs |> CList.map (fun (u1, u2) -> BU.format2 "%s < %s" (show u1) (show u2)) in
    BU.format2 "Solving for %s; inequalities are %s"
                    (show vars) (show ineqs)

let guard_to_string (env:env) g =
  match g.guard_f, view g.deferred with
  | Trivial, VNil when not (Options.print_implicits ()) && is_empty (snd g.univ_ineqs) -> "{}"
  | _ ->
    let form = match g.guard_f with
        | Trivial -> "trivial"
        | NonTrivial f ->
            if !dbg_Rel
            || Debug.extreme ()
            || Options.print_implicits ()
            then N.term_to_string env f
            else "non-trivial"
    in
    let carry defs = CList.map (fun (_, msg, x) -> msg ^ ": " ^ prob_to_string env x) defs |> to_list |> String.concat ",\n" in
    let imps = print_pending_implicits g in
    BU.format5 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits=%s}\n"
      form (carry g.deferred) (carry g.deferred_to_tac)
      (ineqs_to_string g.univ_ineqs) imps

let new_t_problem wl env lhs rel rhs elt loc =
 let reason = if !dbg_ExplainRel
              ||  !dbg_Rel
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

let solve_and_commit wl err
  : option (deferred & deferred & implicits_t) =
  let tx = UF.new_transaction () in

  if !dbg_RelBench then
    BU.print1 "solving problems %s {\n"
      (FStarC.Common.string_of_list (fun p -> string_of_int (p_pid p)) wl.attempting);
  let (sol, ms) = BU.record_time_ms (fun () -> solve wl) in
  if !dbg_RelBench then
    BU.print1 "} solved in %s ms\n" (string_of_int ms);

  match sol with
    | Success (deferred, defer_to_tac, implicits) ->
      let ((), ms) = BU.record_time_ms (fun () -> UF.commit tx) in
      if !dbg_RelBench then
        BU.print1 "committed in %s ms\n" (string_of_int ms);
      Some (deferred, defer_to_tac, implicits)
    | Failed (d,s) ->
      if !dbg_ExplainRel
      ||  !dbg_Rel
      then BU.print_string <| explain wl d s;
      let result = err (d,s) in
      UF.rollback tx;
      result

let with_guard env prob dopt =
    match dopt with
    | None -> None
    | Some (deferred, defer_to_tac, implicits) ->
      def_check_scoped (p_loc prob) "with_guard" env (p_guard prob);
      Some <| simplify_guard env
                ({guard_f=(p_guard prob |> NonTrivial);
                  deferred=deferred;
                  deferred_to_tac=defer_to_tac;
                  univ_ineqs=(empty, empty);
                  implicits=implicits})

let try_teq smt_ok env t1 t2 : option guard_t =
  def_check_scoped t1.pos "try_teq.1" env t1;
  def_check_scoped t2.pos "try_teq.2" env t2;
  // --MLish disables use of SMT. See PR #3123 for explanation.
  let smt_ok = smt_ok && not (Options.ml_ish ()) in
  Profiling.profile
    (fun () ->
      if !dbg_RelTop then
        BU.print3 "try_teq of %s and %s in %s {\n" (show t1) (show t2) (show env.gamma);
      let prob, wl = new_t_problem (empty_worklist env) env t1 EQ t2 None (Env.get_range env) in
      let g = with_guard env prob <| solve_and_commit (singleton wl prob smt_ok) (fun _ -> None) in
      if !dbg_RelTop then
        BU.print1 "} res = %s\n" (FStarC.Common.string_of_option (guard_to_string env) g);
      g)
    (Some (Ident.string_of_lid (Env.current_module env)))
    "FStarC.TypeChecker.Rel.try_teq"


let teq env t1 t2 : guard_t =
    match try_teq true env t1 t2 with
    | None ->
      Err.basic_type_error env env.range None t2 t1;
      trivial_guard
    | Some g ->
        if !dbg_Rel || !dbg_RelTop then
          BU.print3 "teq of %s and %s succeeded with guard %s\n"
                        (show t1) (show t2) (guard_to_string env g);
        g

(*
 * AR: It would be nice to unify it with teq, the way we do it for subtyping
 *     i.e. write a common function that uses a bound variable,
 *          and if the caller requires a prop, close over it, else abstract it
 *     But that may change the existing VCs shape a bit
 *)
let get_teq_predicate env t1 t2 =
    if !dbg_Rel || !dbg_RelTop then
       BU.print2 "get_teq_predicate of %s and %s {\n" (show t1) (show t2);
     let prob, x, wl = new_t_prob (empty_worklist env) env t1 EQ t2 in
     let g = with_guard env prob <| solve_and_commit (singleton wl prob true) (fun _ -> None) in
    if !dbg_Rel || !dbg_RelTop then
       BU.print1 "} res teq predicate = %s\n" (FStarC.Common.string_of_option (guard_to_string env) g);

    match g with
    | None -> None
    | Some g -> Some (abstract_guard (S.mk_binder x) g)

let subtype_fail env e t1 t2 : unit =
  Err.basic_type_error env (Env.get_range env) (Some e) t2 t1

let sub_or_eq_comp env (use_eq:bool) c1 c2 =
  Profiling.profile (fun () ->
    let rel = if use_eq then EQ else SUB in
    if !dbg_Rel || !dbg_RelTop then
      BU.print3 "sub_comp of %s --and-- %s --with-- %s\n" (show c1) (show c2) (if rel = EQ then "EQ" else "SUB");
    let prob, wl = new_problem (empty_worklist env) env c1 rel c2 None (Env.get_range env) "sub_comp" in
    let wl = { wl with repr_subcomp_allowed = true } in
    let prob = CProb prob in
    def_check_prob "sub_comp" prob;
    let (r, ms) = BU.record_time_ms
                  (fun () -> with_guard env prob <| solve_and_commit (singleton wl prob true)  (fun _ -> None))
    in
    if !dbg_Rel || !dbg_RelTop || !dbg_RelBench then
      BU.print4 "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n" (show c1) (show c2) (if rel = EQ then "EQ" else "SUB") (string_of_int ms);
    r)
  (Some (Ident.string_of_lid (Env.current_module env)))
  "FStarC.TypeChecker.Rel.sub_comp"

let sub_comp env c1 c2 =
    Errors.with_ctx "While trying to subtype computation types" (fun () ->
      def_check_scoped c1.pos "sub_comp c1" env c1;
      def_check_scoped c2.pos "sub_comp c2" env c2;
      sub_or_eq_comp env false c1 c2
    )

let eq_comp env c1 c2 =
    Errors.with_ctx "While trying to equate computation types" (fun () ->
      def_check_scoped c1.pos "eq_comp c1" env c1;
      def_check_scoped c2.pos "eq_comp c2" env c2;
      sub_or_eq_comp env true c1 c2
    )

val solve_universe_inequalities' (tx:UF.tx) (env : env_t) (vs_ineqs : clist S.universe & clist (S.universe & S.universe)) : unit
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
     raise_error env Errors.Fatal_IncompatibleUniverse
       (BU.format2 "Universe %s and %s are incompatible" (show u1) (show u2))
   in
   let equiv v v' =
       match SS.compress_univ v, SS.compress_univ v' with
       | U_unif v0, U_unif v0' -> UF.univ_equiv v0 v0'
       | _ -> false
   in
   let sols : clist (S.universe & S.universe) = variables |> CList.collect (fun v ->
     match SS.compress_univ v with
     | U_unif _ -> //if it really is a variable, that try to solve it
         let lower_bounds_of_v : clist S.universe = //lower bounds of v, excluding the other variables
           ineqs |> CList.collect (fun (u, v') ->
             if equiv v v'
             then if variables |> CList.existsb (equiv u)
                  then empty
                  else cons u empty
             else empty)
         in
         let lb = N.normalize_universe env (U_max (lower_bounds_of_v |> to_list)) in
         Listlike.singleton (lb, v)
     | _ ->
       //it may not actually be a variable in case the user provided an explicit universe annnotation
       //see, e.g., ulib/FStar.Universe.fst
      empty) in
   //apply all the solutions
   let _ =
     let wl = {empty_worklist env with defer_ok=NoDefer} in
     sols |> CList.map (fun (lb, v) ->
         //     printfn "Setting %s to its lower bound %s" (show v) (show lb);
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
   if ineqs |> CList.for_all (fun (u, v) ->
        if check_ineq (u, v)
        then true
        else (if !dbg_GenUniverses
              then BU.print2 "%s </= %s" (show u) (show v);
              false))
   then ()
   else (
    if !dbg_GenUniverses then (
       BU.print1 "Partially solved inequality constraints are: %s\n" (ineqs_to_string (variables, ineqs));
       UF.rollback tx; // GM 2024/09/07: It can't be right to rollback on a debug toggle... can it?
       BU.print1 "Original solved inequality constraints are: %s\n" (ineqs_to_string (variables, ineqs))
     );
     raise_error env Errors.Fatal_FailToSolveUniverseInEquality "Failed to solve universe inequalities for inductives"
   )

let solve_universe_inequalities env ineqs : unit =
    let tx = UF.new_transaction () in
    solve_universe_inequalities' tx env ineqs;
    UF.commit tx

let try_solve_deferred_constraints (defer_ok:defer_ok_t) smt_ok deferred_to_tac_ok env (g:guard_t) : guard_t =
  let smt_ok = smt_ok && not (Options.ml_ish ()) in
  Errors.with_ctx "While solving deferred constraints" (fun () ->
  Profiling.profile (fun () ->
   let imps_l = g.implicits |> Listlike.to_list in
   let typeclass_variables =
    imps_l
    |> List.collect
          (fun i ->
            match i.imp_uvar.ctx_uvar_meta with
            | Some (Ctx_uvar_meta_tac tac) ->
              let head, _ = U.head_and_args_full tac in
              if U.is_fvar PC.tcresolve_lid head
              then (
                let goal_type = U.ctx_uvar_typ i.imp_uvar in
                let uvs = Free.uvars goal_type in
                elems uvs
              )
              else []
            | _ -> []) |> Setlike.from_list
   in
   let wl = { wl_of_guard env (to_list g.deferred)
              with defer_ok=defer_ok
                 ; smt_ok=smt_ok
                 ; typeclass_variables } in
   let fail (d,s) =
      let msg = explain wl d s in
      raise_error (p_loc d) Errors.Fatal_ErrorInSolveDeferredConstraints msg
   in
   if !dbg_Rel then
     BU.print4 "Trying to solve carried problems (defer_ok=%s) (deferred_to_tac_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
              (show defer_ok)
              (show deferred_to_tac_ok)
              (show wl)
              (show (List.length imps_l));
   let g =
     match solve_and_commit wl fail with
     | Some (deferred, _, _) when VCons? (view deferred) && defer_ok = NoDefer ->
       failwith "Impossible: Unexpected deferred constraints remain"

     | Some (deferred, defer_to_tac, imps) ->
       {g with deferred=deferred;
               deferred_to_tac=g.deferred_to_tac ++ defer_to_tac;
               implicits = g.implicits ++ imps}

     | _ ->
       failwith "Impossible: should have raised a failure already"
   in
   solve_universe_inequalities env g.univ_ineqs;
   let g =
     if deferred_to_tac_ok
     then Profiling.profile (fun () -> DeferredImplicits.solve_deferred_to_tactic_goals env g)
                            (Some (Ident.string_of_lid (Env.current_module env)))
                            "FStarC.TypeChecker.Rel.solve_deferred_to_tactic_goals"
     else g
   in
   if !dbg_ResolveImplicitsHook
   then BU.print2 "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s (and %s implicits)\n"
          (guard_to_string env g)
          (show (List.length (Listlike.to_list g.implicits)));
   {g with univ_ineqs=(empty, empty)}
  )
  (Some (Ident.string_of_lid (Env.current_module env)))
  "FStarC.TypeChecker.Rel.try_solve_deferred_constraints")


let solve_deferred_constraints env (g:guard_t) =
    let defer_ok = NoDefer in
    let smt_ok = not (Options.ml_ish ()) in
    let deferred_to_tac_ok = true in
    try_solve_deferred_constraints defer_ok smt_ok deferred_to_tac_ok env g

let solve_non_tactic_deferred_constraints maybe_defer_flex_flex env (g:guard_t) =
  Errors.with_ctx "solve_non_tactic_deferred_constraints" (fun () ->
    def_check_scoped Range.dummyRange "solve_non_tactic_deferred_constraints.g" env g;
    let defer_ok = if maybe_defer_flex_flex then DeferFlexFlexOnly else NoDefer in
    let smt_ok = not (Options.ml_ish ()) in
    let deferred_to_tac_ok = false in
    try_solve_deferred_constraints defer_ok smt_ok deferred_to_tac_ok env g
  )

let do_discharge_vc use_env_range_msg env vc : unit =
  let open FStarC.Pprint in
  let open FStarC.Errors.Msg in
  let open FStarC.Class.PP in
  let debug : bool = !dbg_Rel || !dbg_SMTQuery || !dbg_Discharge in
  let diag = Errors.diag (Env.get_range env) #(list document) in // FIXME: without the implicit, batch mode fails during generalization
  if debug then
    diag [text "Checking VC:" ^/^ pp vc];

  (* Tactic preprocessing *)
  let vcs : list (env_t & typ & Options.optionstate) = (
    if Options.use_tactics() then begin
      Options.with_saved_options (fun () ->
        ignore <| Options.set_options "--no_tactics";
        let did_anything, vcs = env.solver.preprocess env vc in
        if debug && did_anything then
          diag [text "Tactic preprocessing produced" ^/^ pp (List.length vcs <: int) ^/^ text "goals"];
        let vcs = vcs |> List.map (fun (env, goal, opts) ->
                            // NB: No Eager_unfolding. Why?
                            env,
                            norm_with_steps "FStarC.TypeChecker.Rel.norm_with_steps.7"
                                            [Env.Simplify; Env.Primops; Env.Exclude Env.Zeta] env goal,
                            opts)
        in

        (* handle_smt_goals: users can register a tactic to run on all
           remaining goals after tactic execution. *)
        let vcs = vcs |> List.concatMap (fun (env, goal, opts) ->
          env.solver.handle_smt_goal env goal |>
            (* Keep the same SMT options *)
            List.map (fun (env, goal) -> (env, goal, opts)))
        in

        (* discard trivial goals *)
        let vcs = vcs |> List.concatMap (fun (env, goal, opts) ->
          match check_trivial goal with
          | Trivial ->
            if debug then
              diag [text "Goal completely solved by tactic\n"];
            []

          | NonTrivial goal ->
            [(env, goal, opts)]
        )
        in
        vcs
      )
    end
    else [env, vc, FStarC.Options.peek ()]
    )
  in

  (* Splitting queries. FIXME: isn't this redundant given the
  code in SMTEncoding.Solver? *)
  let vcs =
    if Options.split_queries () = Options.Always
    then vcs |>
          List.collect
            (fun (env, goal, opts) ->
                match Env.split_smt_query env goal with
                | None -> [env,goal,opts]
                | Some goals -> goals |> List.map (fun (env, goal) -> env,goal,opts))
    else vcs
  in

  (* Solve one by one. If anything fails the SMT module will log errors. *)
  vcs |> List.iter (fun (env, goal, opts) ->
    Options.with_saved_options (fun () ->
      FStarC.Options.set opts;
      (* diag (BU.format2 "Trying to solve:\n> %s\nWith proof_ns:\n %s\n" *)
      (*                   (show goal) (Env.string_of_proof_ns env)); *)
      if debug then
        diag [text "Before calling solver, VC =" ^/^ pp goal];
      env.solver.solve use_env_range_msg env goal
    )
  )

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
let discharge_guard' use_env_range_msg env (g:guard_t) (use_smt:bool) : option guard_t =
  if !dbg_ResolveImplicitsHook
  then BU.print1 "///////////////////ResolveImplicitsHook: discharge_guard'\n\
                  guard = %s\n"
                  (guard_to_string env g);

  let g =
    let defer_ok = NoDefer in
    let smt_ok = not (Options.ml_ish ()) && use_smt in
    let deferred_to_tac_ok = true in
    try_solve_deferred_constraints defer_ok smt_ok deferred_to_tac_ok env g
  in
  let open FStarC.Pprint in
  let open FStarC.Errors.Msg in
  let open FStarC.Class.PP in
  let debug : bool = !dbg_Rel || !dbg_SMTQuery || !dbg_Discharge in
  let diag = Errors.diag (Env.get_range env) #(list document) in
  let ret_g = {g with guard_f = Trivial} in
  if env.admit then (
    let open FStarC.Class.PP in
    if debug && not (Trivial? g.guard_f) && not env.phase1 then
      diag [
        text "Skipping VC because verification is disabled.";
        text "VC =" ^/^ pp g;
      ];
    Some ret_g
  ) else (
    let g = simplify_guard_full_norm env g in
    match g.guard_f with
    | Trivial ->
      Some ret_g

    | NonTrivial vc when not use_smt ->
      if debug then
        diag [text "Cannot solve without SMT:" ^/^ pp vc];
      None

    | NonTrivial vc ->
      do_discharge_vc use_env_range_msg env vc;
      Some ret_g
  )

let discharge_guard env g =
  match discharge_guard' None env g true with
  | Some g -> g
  | None  -> failwith "Impossible, with use_smt = true, discharge_guard' should never have returned None"

let discharge_guard_no_smt env g =
  match discharge_guard' None env g false with
  | Some g -> g
  | None ->
    raise_error env Errors.Fatal_ExpectTrivialPreCondition [
      text "Expected a trivial pre-condition"
    ]

let teq_nosmt (env:env) (t1:typ) (t2:typ) : option guard_t =
  match try_teq false env t1 t2 with
  | None -> None
  | Some g -> discharge_guard' None env g false

let subtype_nosmt env t1 t2 =
    if !dbg_Rel || !dbg_RelTop
    then BU.print2 "try_subtype_no_smt of %s and %s\n" (N.term_to_string env t1) (N.term_to_string env t2);
    let prob, x, wl = new_t_prob (empty_worklist env) env t1 SUB t2 in
    let g = with_guard env prob <| solve_and_commit (singleton wl prob false) (fun _ -> None) in
    match g with
    | None -> None
    | Some g ->
      let g = close_guard env [S.mk_binder x] g in
      discharge_guard' None env g false

///////////////////////////////////////////////////////////////////
let check_subtyping env t1 t2 =
  Profiling.profile (fun () ->
    if !dbg_Rel || !dbg_RelTop
    then BU.print2 "check_subtyping of %s and %s\n" (N.term_to_string env t1) (N.term_to_string env t2);
    let prob, x, wl = new_t_prob (empty_worklist env) env t1 SUB t2 in
    let env_x = Env.push_bv env x in
    let smt_ok = not (Options.ml_ish ()) in
    let g = with_guard env_x prob <| solve_and_commit (singleton wl prob smt_ok) (fun _ -> None) in
    match g with
    | None -> (
      if !dbg_Rel || !dbg_RelTop then
        BU.print2 "check_subtyping FAILED: %s <: %s\n"
                      (N.term_to_string env_x t1)
                      (N.term_to_string env_x t2);
        None
    )
    | Some g -> (
      if !dbg_Rel || !dbg_RelTop then
        BU.print3 "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                      (N.term_to_string env_x t1)
                      (N.term_to_string env_x t2)
                      (guard_to_string env_x g);
      Some (x, g)
    )
  )
  (Some (Ident.string_of_lid (Env.current_module env)))
  "FStarC.TypeChecker.Rel.check_subtyping"

let get_subtyping_predicate env t1 t2 =
  Errors.with_ctx "While trying to get a subtyping predicate" (fun () ->
    def_check_scoped t1.pos "get_subtyping_predicate.1" env t1;
    def_check_scoped t2.pos "get_subtyping_predicate.2" env t2;
    match check_subtyping env t1 t2 with
    | None -> None
    | Some (x, g) ->
      Some (abstract_guard (S.mk_binder x) g)
  )

let get_subtyping_prop env t1 t2 =
  Errors.with_ctx "While trying to get a subtyping proposition" (fun () ->
    def_check_scoped t1.pos "get_subtyping_prop.1" env t1;
    def_check_scoped t2.pos "get_subtyping_prop.2" env t2;
    match check_subtyping env t1 t2 with
    | None -> None
    | Some (x, g) ->
      Some (close_guard env [S.mk_binder x] g)
  )

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

let try_solve_single_valued_implicits env is_tac (imps:Env.implicits) : Env.implicits & bool =
  (*
   * Get the value of the implicit imp
   * Going forward, it can also return new implicits for the pattern variables
   *   (cf. the comment above about extending it to inductives)
   *)
  if is_tac then imps, false
  else
    let imp_value imp : option term =
      let ctx_u, r = imp.imp_uvar, imp.imp_range in

     let t_norm = N.normalize N.whnf_steps env (U.ctx_uvar_typ ctx_u) in

      match (SS.compress t_norm).n with
      | Tm_fvar fv when S.fv_eq_lid fv PC.unit_lid ->
        r |> S.unit_const_with_range |> Some
      | Tm_refine {b} when U.is_unit b.sort ->
        r |> S.unit_const_with_range |> Some
      | _ -> None in

    let b = List.fold_left (fun b imp ->  //check that the imp is still unsolved
      if UF.find imp.imp_uvar.ctx_uvar_head |> is_none &&
         U.ctx_uvar_should_check imp.imp_uvar = Strict
      then match imp_value imp with
           | Some tm -> commit env ([TERM (imp.imp_uvar, tm)]); true
           | None -> b
      else b) false imps in

    imps, b

(*
 * Check that an implicit solution has the expected type
 *
 * Return None if we did not typecheck the implicit because
 *   typechecking it required solving deferred univ constraints,
 *   and the flag force_univ_constraints is not set
 *
 * Invariants:
 *   - If force_univ_constraints is set, return is a Some
 *   - If is_tac is true, return is Some []
 *   - The caller (resolve_implicits') ensures that
 *     if is_tac then force_univ_constraints
 *
 *)
let check_implicit_solution_and_discharge_guard env
  (imp:implicit)
  (is_tac force_univ_constraints:bool)

  : option TcComm.implicits_t =

  let {imp_reason; imp_tm; imp_uvar; imp_range} = imp in

  let uvar_ty = U.ctx_uvar_typ imp_uvar in
  let uvar_should_check = U.ctx_uvar_should_check imp_uvar in

  if !dbg_Rel
  then BU.print5 "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
         (show imp_uvar.ctx_uvar_head)
         (show imp_tm)
         (show uvar_ty)
         imp_reason
         (Range.string_of_range imp_range);

  let env =
    {env with gamma=imp_uvar.ctx_uvar_gamma}
    |> Env.clear_expected_typ
    |> fst in

  let g =
    Errors.with_ctx
      "While checking implicit solution"
      (fun () ->
       let skip_core =
         env.phase1 ||
         env.admit ||
         Allow_untyped? uvar_should_check ||
         Already_checked? uvar_should_check in

       let must_tot = not (env.phase1 ||
                           env.admit ||
                           Allow_ghost? uvar_should_check) in

       if skip_core
       then if is_tac
            then Env.trivial_guard
            else begin  // following is ad-hoc code for constraining some univs
                        // ideally we should get rid of it, and just return trivial_guard
              (*
               * AR: when we create lambda terms as solutions to implicits (in u_abs),
               *       we set the type in the residual comp to be the type of the uvar
               *     while this ok for smt encoding etc., when we are typechecking the implicit solution using fastpath,
               *       it doesn't help since the two types are the same (the type of the uvar and its solution)
               *     worse, this prevents some constraints to be generated between the actual type of the solution
               *       and the type of the uvar
               *     therefore, we unset the residual comp type in the solution before typechecking
               *)
              let imp_tm =
                match (SS.compress imp_tm).n with
                | Tm_abs {bs; body; rc_opt=Some rc} ->
                  {imp_tm with n=Tm_abs {bs; body; rc_opt=Some ({rc with residual_typ=None})}}
                | _ -> imp_tm in

              let k', g =
                env.typeof_well_typed_tot_or_gtot_term
                  env
                  imp_tm must_tot in

              match get_subtyping_predicate env k' uvar_ty with
              | None -> Err.expected_expression_of_type env imp_tm.pos uvar_ty imp_tm k'
              | Some f ->
                {Env.conj_guard (Env.apply_guard f imp_tm) g with guard_f=Trivial}
            end
       else begin
         match env.core_check env imp_tm uvar_ty must_tot with
         | Inl None -> trivial_guard
         | Inl (Some g) -> { trivial_guard with guard_f = NonTrivial g }
         | Inr print_err ->
           raise_error imp_range Errors.Fatal_FailToResolveImplicitArgument
             (BU.format5 "Core checking failed for implicit %s (is_tac: %s) (reason: %s) (%s <: %s)"
                  (show imp_uvar) (show is_tac) imp_reason (show imp_tm) (show uvar_ty))
       end) in

  if (not force_univ_constraints) &&
     (CList.existsb (fun (reason, _, _) -> reason = Deferred_univ_constraint) g.deferred)
  then None
  else let g' =
         match discharge_guard'
                 (Some (fun () ->
                        BU.format4 "%s (Introduced at %s for %s resolved at %s)"
                          (show imp_tm) (show imp_range) imp_reason (show imp_tm.pos)))
                   env g true with
         | Some g -> g
         | None -> failwith "Impossible, with use_smt = true, discharge_guard' must return Some" in
       g'.implicits |> Some

(*
 * resolve_implicits' uses it to determine if a ctx uvar is unresolved
 *)
let rec unresolved ctx_u : bool =
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


(*
 * In the fixpoint loop of resolve_implicits',
 *   when we reach a fixpoint, with some implicits still remaining,
 * try to pick an implicit whose typechecking generates a univ constraint,
 *   force it, and then repeat the fixpoint loop
 *)
let pick_a_univ_deffered_implicit (out : tagged_implicits)
  : option Env.implicit & tagged_implicits
  =
  let imps_with_deferred_univs, rest = List.partition
    (fun (_, status) -> status = Implicit_checking_defers_univ_constraint)
    out in
  match imps_with_deferred_univs with
  | [] -> None, out
  | hd::tl -> hd |> fst |> Some, (tl@rest)

let is_tac_implicit_resolved (env:env) (i:implicit) : bool =
    i.imp_tm
    |> Free.uvars
    |> Setlike.for_all (fun uv -> Allow_unresolved? (U.ctx_uvar_should_check uv))


// is_tac: this is a call from within the tactic engine, hence do not use
//         tactics for resolving implicits to avoid reentrancy.
//
// is_gen: this is a call after generalization, hence we only check that
//         implicits have a solution, and do not typecheck it. This still allows
//         some implicits to remain unresolved, but those will remain in the guard.
let resolve_implicits' env is_tac is_gen (implicits:Env.implicits)
  : list (implicit & implicit_checking_status) =
  
  (* Meta argument cache: during a single run of this resolve_implicits' function
  we keep track of all results of the "cacheable" tactics that are used for meta
  arguments. The only cacheable tactic, for now, is tcresolve. Before trying to run
  it, we check the cache to see if we have already solved a problem in the same environment
  and for the same uvar type (in this case, the constraint). If so, we just take that result.

  This is pretty conservative. e.g. in
    f (1 + 1);
    g (1 + 1)
  we cannot reuse the solution for each +, since there is an extra unit binder when
  we check `g ...`. But it does lead to big gains in expressions like `1 + 1 + 1 ...`. *)
  let cacheable tac =
    (* Detect either an unapplied tcresolve or an eta expanded variant. This is
    mostly in support of solve, which has to be written eta expanded. *)
    (U.is_fvar PC.tcresolve_lid tac) || (
      match (SS.compress tac).n with
      | Tm_abs ({bs=[_]; body}) ->
        let hd, args = U.head_and_args body in
        U.is_fvar PC.tcresolve_lid hd && List.length args = 1
      | _ -> false
    )
  in
  (* tcresolve is also the only tactic we ever run for an open problem. *)
  let meta_tac_allowed_for_open_problem tac = cacheable tac in
  let __meta_arg_cache : ref (list (term & env_t & typ & term)) = BU.mk_ref [] in
  let meta_arg_cache_result (tac : term) (e : env_t) (ty : term) (res : term) : unit =
    __meta_arg_cache := (tac, e, ty, res) :: !__meta_arg_cache
  in
  let meta_arg_cache_lookup (tac : term) (e : env_t) (ty : term) : option term =
    let rec aux l : option term =
      match l with
      | [] -> None
      | (tac', e', ty', res') :: l' ->
        if U.term_eq tac tac'
           && FStarC.Common.eq_list U.eq_binding e.gamma e'.gamma
           && U.term_eq ty ty'
        then Some res'
        else aux l'
    in
    aux !__meta_arg_cache
  in
  (* / cache *) 

  let rec until_fixpoint (acc : tagged_implicits & (*changed:*)bool & (*defer_open_metas:*)bool )
                         (implicits:Env.implicits) 
    : tagged_implicits =

    let out, changed, defer_open_metas = acc in
    (* changed: we made some progress
       defer_open_metas: starts at true, it means to not try to run
         meta arg tactics in environments/types that have unresolved
         uvars. We first do a pass with this set to true, and if nothing
         changed, we then give up and set it to false, trying to eagerly
         solve some partially-unresolved constraints. This is definitely
         not ideal, maybe the right thing to do is to never run metas
         in open contexts, but that is raising many regressions rihgt now,
         particularly in Steel (which uses the resolve_implicits hook pervasively). *)

    match implicits with
    | [] ->
      if changed then (
        (* We made some progress, keep going from the start *)
        until_fixpoint ([], false, true) (List.map fst out)
      ) else if defer_open_metas then (
        (* No progress... but we could try being more eager with metas. *)
        until_fixpoint ([], false, false) (List.map fst out)
      ) else (
           //Nothing changed in this iteration of the loop
           //We will try to make progress by either solving a single valued implicit,
           //  or solving an implicit that generates univ constraint, with force flag on
           let imps, changed = try_solve_single_valued_implicits env is_tac (List.map fst out) in
           if changed then until_fixpoint ([], false, true) imps
           else let imp_opt, rest = pick_a_univ_deffered_implicit out in
                (match imp_opt with
                 | None -> rest  //No such implicit exists, return remaining implicits
                 | Some imp ->
                   let force_univ_constraints = true in
                   let imps =
                     check_implicit_solution_and_discharge_guard
                       env
                       imp
                       is_tac
                       force_univ_constraints |> must in
                   until_fixpoint ([], false, true) (Listlike.to_list imps ++ List.map fst rest))
      )

    | hd::tl ->
      let { imp_reason = reason; imp_tm = tm; imp_uvar = ctx_u; imp_range = r } = hd in
      let { uvar_decoration_typ; uvar_decoration_should_check } = UF.find_decoration ctx_u.ctx_uvar_head in
      if !dbg_Rel then
        BU.print4 "resolve_implicits' loop, imp_tm=%s and ctx_u=%s, is_tac=%s, should_check=%s\n"
             (show tm) (show ctx_u) (show is_tac) (show uvar_decoration_should_check);
      begin match () with
      | _ when Allow_unresolved? uvar_decoration_should_check ->
        until_fixpoint (out, true, defer_open_metas) tl

      | _ when unresolved ctx_u && flex_uvar_has_meta_tac ctx_u ->
        let Some (Ctx_uvar_meta_tac tac) = ctx_u.ctx_uvar_meta in
        let env = { env with gamma = ctx_u.ctx_uvar_gamma } in
        let typ = U.ctx_uvar_typ ctx_u in
        let is_open = has_free_uvars typ || gamma_has_free_uvars ctx_u.ctx_uvar_gamma in
        if defer_open_metas && is_open then (
          (* If the result type or env for this meta arg has a free uvar, delay it.
          Some other meta arg being solved may instantiate the uvar. See #3130. *)
          if !dbg_Rel || !dbg_Imps then
            BU.print1 "Deferring implicit due to open ctx/typ %s\n" (show ctx_u);
          until_fixpoint ((hd, Implicit_unresolved)::out, changed, defer_open_metas) tl
        ) else if is_open && not (meta_tac_allowed_for_open_problem tac)
            && Options.Ext.get "compat:open_metas" = "" then ( // i.e. compat option unset
          (* If the tactic is not explicitly whitelisted to run with open problems,
          then defer. *)
          until_fixpoint ((hd, Implicit_unresolved)::out, changed, defer_open_metas) tl
        ) else (
          let solve_with (t:term) =
            let extra =
              match teq_nosmt env t tm with
              | None -> failwith "resolve_implicits: unifying with an unresolved uvar failed?"
              | Some g -> Listlike.to_list g.implicits
            in
            until_fixpoint (out, true, defer_open_metas) (extra @ tl)
          in
          if cacheable tac then
            match meta_arg_cache_lookup tac env typ with
            | Some res -> solve_with res
            | None ->
              let t = run_meta_arg_tac env ctx_u in
              meta_arg_cache_result tac env typ t;
              solve_with t
          else
            let t = run_meta_arg_tac env ctx_u in
            solve_with t
        )

      | _ when unresolved ctx_u ->
        until_fixpoint ((hd, Implicit_unresolved)::out, changed, defer_open_metas) tl

      | _ when Allow_untyped? uvar_decoration_should_check ||
               Already_checked? uvar_decoration_should_check ||
               is_gen ->
        until_fixpoint (out, true, defer_open_metas) tl
      | _ ->
        let env = {env with gamma=ctx_u.ctx_uvar_gamma} in
        (*
         * AR: Some opportunities for optimization here,
         *       we may end up normalizing an implicit solution multiple times in
         *       multiple until_fixpoint calls
         *)
        let tm = norm_with_steps "FStarC.TypeChecker.Rel.norm_with_steps.8" [Env.Beta] env tm in
        let hd = {hd with imp_tm=tm} in
        if is_tac
        then begin
          if is_tac_implicit_resolved env hd
          then let force_univ_constraints = true in
               let res = check_implicit_solution_and_discharge_guard
                 env
                 hd
                 is_tac
                 force_univ_constraints in
               let res = BU.map_opt res Listlike.to_list in
               if res <> Some []
               then failwith "Impossible: check_implicit_solution_and_discharge_guard for tac must return Some []"
               else ()
          else ();
          until_fixpoint (out, true, defer_open_metas) tl
        end
        else
        begin
          let force_univ_constraints = false in
          let imps_opt =
            check_implicit_solution_and_discharge_guard
              env
              hd
              is_tac
              force_univ_constraints in

          match imps_opt with
          | None ->
            until_fixpoint ((hd, Implicit_checking_defers_univ_constraint)::out, changed, defer_open_metas) tl  //Move hd to out
          | Some imps ->
            //add imps to out
            until_fixpoint ((imps |> Listlike.to_list |> List.map (fun i -> i, Implicit_unresolved))@out, true, defer_open_metas) tl
        end
      end
  in
  until_fixpoint ([], false, true) implicits

let resolve_implicits env g =
    if !dbg_ResolveImplicitsHook
    then BU.print1 "//////////////////////////ResolveImplicitsHook: resolve_implicits begin////////////\n\
                    guard = %s {\n"
                    (guard_to_string env g);
    let tagged_implicits = resolve_implicits' env false false (Listlike.to_list g.implicits) in
    if !dbg_ResolveImplicitsHook
    then BU.print_string "//////////////////////////ResolveImplicitsHook: resolve_implicits end////////////\n\
                    }\n";
    {g with implicits = Listlike.from_list <| List.map fst tagged_implicits}

let resolve_generalization_implicits env g =
    let tagged_implicits = resolve_implicits' env false true (Listlike.to_list g.implicits) in
    {g with implicits = Listlike.from_list <| List.map fst tagged_implicits}

let resolve_implicits_tac env g = resolve_implicits' env true false (Listlike.to_list g.implicits)

let force_trivial_guard env g =
    if !dbg_ResolveImplicitsHook
    then BU.print1 "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\n\
                    guard = %s\n"
                    (guard_to_string env g);
    let g = solve_deferred_constraints env g in
    let g = resolve_implicits env g in
    match Listlike.to_list g.implicits with
    | [] -> ignore <| discharge_guard env g
    | imp::_ ->
      let open FStarC.Pprint in
      raise_error imp.imp_range Errors.Fatal_FailToResolveImplicitArgument [
        prefix 4 1 (text "Failed to resolve implicit argument")
                (arbitrary_string (show imp.imp_uvar.ctx_uvar_head)) ^/^
        prefix 4 1 (text "of type")
                (N.term_to_doc env (U.ctx_uvar_typ imp.imp_uvar)) ^/^
        prefix 4 1 (text "introduced for")
                (text imp.imp_reason)
      ]

let subtype_nosmt_force env t1 t2 =
    match subtype_nosmt env t1 t2 with
    | None -> false
    | Some g ->
        force_trivial_guard env g;
        true

let teq_force (env:env) (t1:typ) (t2:typ) : unit =
    force_trivial_guard env (teq env t1 t2)

let teq_nosmt_force (env:env) (t1:typ) (t2:typ) :bool =
    match teq_nosmt env t1 t2 with
    | None -> false
    | Some g ->
        force_trivial_guard env g;
        true

let layered_effect_teq env (t1:term) (t2:term) (reason:option string) : guard_t =
  if !dbg_LayeredEffectsEqns
  then BU.print3 "Layered Effect (%s) %s = %s\n"
         (if reason |> is_none then "_" else reason |> must)
         (show t1) (show t2);
  teq env t1 t2  //AR: teq_nosmt?


let universe_inequality (u1:universe) (u2:universe) : guard_t =
    //Printf.printf "Universe inequality %s <= %s\n" (show u1) (show u2);
    {trivial_guard with univ_ineqs=(empty, cons (u1,u2) empty)}

(*
   Copyright 2008-2016 Microsoft Research

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
module FStarC.Tactics.V1.Basic

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Util
open FStarC.Ident
open FStarC.TypeChecker.Env
open FStarC.TypeChecker.Common
open FStarC.Reflection.V1.Data
open FStarC.Reflection.V1.Builtins
open FStarC.Tactics.Result
open FStarC.Tactics.Types
open FStarC.Tactics.Monad
open FStarC.Tactics.Printing
open FStarC.Syntax.Syntax
open FStarC.VConfig
open FStarC.Class.Show
open FStarC.Class.Tagged
module Listlike = FStarC.Class.Listlike

module BU     = FStarC.Util
module Cfg    = FStarC.TypeChecker.Cfg
module Env    = FStarC.TypeChecker.Env
module Err    = FStarC.Errors
module N      = FStarC.TypeChecker.Normalize
module PC     = FStarC.Parser.Const
module Print  = FStarC.Syntax.Print
module Free   = FStarC.Syntax.Free
module Rel    = FStarC.TypeChecker.Rel
module SF     = FStarC.Syntax.Free
module S      = FStarC.Syntax.Syntax
module SS     = FStarC.Syntax.Subst
module TcComm = FStarC.TypeChecker.Common
module TcTerm = FStarC.TypeChecker.TcTerm
module UF     = FStarC.Syntax.Unionfind
module U      = FStarC.Syntax.Util
module Z      = FStarC.BigInt
module Core   = FStarC.TypeChecker.Core
module PO     = FStarC.TypeChecker.Primops

open FStarC.Class.Monad
open FStarC.Class.Setlike

let dbg_2635     = Debug.get_toggle "2635"
let dbg_ReflTc   = Debug.get_toggle "ReflTc"
let dbg_Tac      = Debug.get_toggle "Tac"
let dbg_TacUnify = Debug.get_toggle "TacUnify"

let ret #a (x:a) : tac a = return x
let bind #a #b : tac a -> (a -> tac b) -> tac b = ( let! )
let idtac : tac unit = return ()
(* This is so we can use the monad class. But we don't want to
rewrite this whole (deprecated) file. *)

(* Internal, repeated from V2 too. Could be in Types, but that
constrains dependencies and F* claims a cycle. *)
let get_phi (g:goal) : option term = U.un_squash (N.unfold_whnf (goal_env g) (goal_type g))
let is_irrelevant (g:goal) : bool = Option.isSome (get_phi g)

let core_check env sol t must_tot
  : either (option typ) Core.error
  = if not (Options.compat_pre_core_should_check()) then Inl None else
    let debug f =
        if Debug.any()
        then f ()
        else ()
    in
    match FStarC.TypeChecker.Core.check_term env sol t must_tot with
    | Inl None ->
      Inl None

    | Inl (Some g) ->
      if Options.compat_pre_core_set ()  //core check the solution, but drop the guard, pre_core
      then Inl None
      else Inl (Some g)


    | Inr err ->
      debug (fun _ ->
               BU.print5 "(%s) Core checking failed (%s) on term %s and type %s\n%s\n"
                         (show (Env.get_range env))
                         (Core.print_error_short err)
                         (show sol)
                         (show t)
                         (Core.print_error err));
      Inr err

type name = bv
type env = Env.env
type implicits = Env.implicits

let rangeof g = g.goal_ctx_uvar.ctx_uvar_range

// Beta reduce
let normalize s e t = N.normalize s e t
let bnorm e t = normalize [] e t
let whnf e t = N.unfold_whnf e t

(* Use this one for everything the user is supposed to see, EXCEPT
 * STATE DUMPS, as it does resugaring. For debug messages, just use plain
 * term_to_string, we don't want to cause normalization with debug
 * flags. *)
let tts = N.term_to_string

let set_uvar_expected_typ (u:ctx_uvar) (t:typ)
  : unit
  = let dec = UF.find_decoration u.ctx_uvar_head in
    UF.change_decoration u.ctx_uvar_head ({dec with uvar_decoration_typ = t })

let mark_uvar_with_should_check_tag (u:ctx_uvar) (sc:should_check_uvar)
  : unit
  = let dec = UF.find_decoration u.ctx_uvar_head in
    UF.change_decoration u.ctx_uvar_head ({dec with uvar_decoration_should_check = sc })

let mark_uvar_as_already_checked (u:ctx_uvar)
  : unit
  = mark_uvar_with_should_check_tag u Already_checked

let mark_goal_implicit_already_checked (g:goal)
  : unit
  = mark_uvar_as_already_checked g.goal_ctx_uvar

let goal_with_type g t
  : goal
  = let u = g.goal_ctx_uvar in
    set_uvar_expected_typ u t;
    g

let bnorm_goal g = goal_with_type g (bnorm (goal_env g) (goal_type g))

let tacprint  (s:string)       = BU.print1 "TAC>> %s\n" s
let tacprint1 (s:string) x     = BU.print1 "TAC>> %s\n" (BU.format1 s x)
let tacprint2 (s:string) x y   = BU.print1 "TAC>> %s\n" (BU.format2 s x y)
let tacprint3 (s:string) x y z = BU.print1 "TAC>> %s\n" (BU.format3 s x y z)

let print (msg:string) : tac unit =
    if not (Options.silent ()) || Options.interactive () then
      tacprint msg;
    ret ()

let debugging () : tac bool =
    bind get (fun ps ->
    ret !dbg_Tac)

let do_dump_ps (msg:string) (ps:proofstate) : unit =
  let psc = ps.psc in
  let subst = PO.psc_subst psc in
  do_dump_proofstate ps msg

let dump (msg:string) : tac unit =
  mk_tac (fun ps ->
    do_dump_ps msg ps;
    Success ((), ps))

let dump_all (print_resolved:bool) (msg:string) : tac unit =
  mk_tac (fun ps ->
    (* Make a new proofstate with goals for each implicit,
     * print it, and return original proofstate unchanged. *)
    let gs = List.map (fun i -> goal_of_implicit ps.main_context i) ps.all_implicits in
    let gs =
     if print_resolved
     then gs
     else List.filter (fun g -> not (check_goal_solved g)) gs
    in
    let ps' = { ps with smt_goals = [] ; goals = gs } in
    do_dump_ps msg ps';
    Success ((), ps))

let dump_uvars_of (g:goal) (msg:string) : tac unit =
  mk_tac (fun ps ->
    let uvs = SF.uvars (goal_type g) |> elems in
    let gs = List.map (goal_of_ctx_uvar g) uvs in
    let gs = List.filter (fun g -> not (check_goal_solved g)) gs in
    let ps' = { ps with smt_goals = [] ; goals = gs } in
    do_dump_ps msg ps';
    Success ((), ps))

let fail1 msg x     = fail (BU.format1 msg x)
let fail2 msg x y   = fail (BU.format2 msg x y)
let fail3 msg x y z = fail (BU.format3 msg x y z)
let fail4 msg x y z w = fail (BU.format4 msg x y z w)

let destruct_eq' (typ : typ) : option (term & term) =
    let open FStarC.Syntax.Formula in
    match destruct_typ_as_formula typ with
    | Some (BaseConn(l, [_; (e1, None); (e2, None)]))
      when Ident.lid_equals l PC.eq2_lid
      ||   Ident.lid_equals l PC.c_eq2_lid
      ->
        Some (e1, e2)
    | _ ->
      match U.unb2t typ with
      | None -> None
      | Some t ->
        begin
        let hd, args = U.head_and_args t in
        match (SS.compress hd).n, args with
        | Tm_fvar fv, [(_, Some ({ aqual_implicit = true })); (e1, None); (e2, None)] when S.fv_eq_lid fv PC.op_Eq ->
            Some (e1, e2)
        | _ -> None
        end

let destruct_eq (env : Env.env) (typ : typ) : option (term & term) =
// TODO: unascribe?
    let typ = whnf env typ in
    match destruct_eq' typ with
    | Some t -> Some t
    | None ->
        // Retry for a squashed one
        begin match U.un_squash typ with
        | Some typ ->
          let typ = whnf env typ in
          destruct_eq' typ
        | None -> None
        end


let get_guard_policy () : tac guard_policy =
    bind get (fun ps -> ret ps.guard_policy)

let set_guard_policy (pol : guard_policy) : tac unit =
    bind get (fun ps -> set ({ ps with guard_policy = pol }))

let with_policy pol (t : tac 'a) : tac 'a =
    bind (get_guard_policy ()) (fun old_pol ->
    bind (set_guard_policy pol) (fun () ->
    bind t (fun r ->
    bind (set_guard_policy old_pol) (fun () ->
    ret r))))

let proc_guard' (simplify:bool) (reason:string) (e : env) (g : guard_t) (sc_opt:option should_check_uvar) (rng:Range.range) : tac unit =
    mlog (fun () ->
        BU.print2 "Processing guard (%s:%s)\n" reason (Rel.guard_to_string e g)) (fun () ->
    let imps = Listlike.to_list g.implicits in 
    let _ =
      match sc_opt with
      | Some (Allow_untyped r) ->
        List.iter
          (fun imp -> mark_uvar_with_should_check_tag imp.imp_uvar (Allow_untyped r))
          imps
      | _ -> ()
    in
    add_implicits imps ;!
    let guard_f =
      if simplify
      then (Rel.simplify_guard e g).guard_f
      else g.guard_f
    in
    match guard_f with
    | TcComm.Trivial -> ret ()
    | TcComm.NonTrivial f ->
      let! ps = get in
      match ps.guard_policy with
      | Drop ->
        // should somehow taint the state instead of just printing a warning
        Err.log_issue e Errors.Warning_TacAdmit
          (BU.format1 "Tactics admitted guard <%s>\n\n" (Rel.guard_to_string e g));
        ret ()

      | Goal ->
        mlog (fun () -> BU.print2 "Making guard (%s:%s) into a goal\n" reason (Rel.guard_to_string e g)) (fun () ->
        let! g = goal_of_guard reason e f sc_opt rng in
        push_goals [g])

      | SMT ->
        mlog (fun () -> BU.print2 "Pushing guard (%s:%s) as SMT goal\n" reason (show f)) (fun () ->
        let! g = goal_of_guard reason e f sc_opt rng in
        push_smt_goals [g])

      | SMTSync ->
        mlog (fun () -> BU.print2 "Sending guard (%s:%s) to SMT Synchronously\n" reason (show f)) (fun () ->
        Rel.force_trivial_guard e g;
        ret ())

    | Force ->
        mlog (fun () -> BU.print2 "Forcing guard (%s:%s)\n" reason (Rel.guard_to_string e g)) (fun () ->
        try if not (Env.is_trivial <| Rel.discharge_guard_no_smt e g)
            then
                mlog (fun () -> BU.print1 "guard = %s\n" (Rel.guard_to_string e g)) (fun () ->
                fail1 "Forcing the guard failed (%s)" reason)
            else ret ()
        with
        | _ -> mlog (fun () -> BU.print1 "guard = %s\n" (Rel.guard_to_string e g)) (fun () ->
               fail1 "Forcing the guard failed (%s)" reason)))

let proc_guard = proc_guard' true

//
// See if any of the implicits in uvs were solved in a Rel call,
//   if so, core check them
//
let tc_unifier_solved_implicits env (must_tot:bool) (allow_guards:bool) (uvs:list ctx_uvar) : tac unit =
  let aux (u:ctx_uvar) : tac unit =
    let dec = UF.find_decoration u.ctx_uvar_head in
    let sc = dec.uvar_decoration_should_check in
    match sc with
    | Allow_untyped _ ->
      ret ()
    | Already_checked ->
      ret ()
    | _ ->
      match UF.find u.ctx_uvar_head with
      | None ->
        ret () //not solved yet
      | Some sol ->  //solved, check it
        let env = {env with gamma=u.ctx_uvar_gamma} in
        let must_tot = must_tot && not (Allow_ghost? dec.uvar_decoration_should_check) in
        match core_check env sol (U.ctx_uvar_typ u) must_tot with
        | Inl None ->
          //checked with no guard
          //no need to check it again
          mark_uvar_as_already_checked u;
          ret ()

        | Inl (Some g) ->
          let guard = { Env.trivial_guard with guard_f = NonTrivial g } in
          let guard = Rel.simplify_guard env guard in
          if Options.disallow_unification_guards ()
          && not allow_guards
          && NonTrivial? guard.guard_f
          then (
            fail3 "Could not typecheck unifier solved implicit %s to %s since it produced a guard and guards were not allowed;guard is\n%s"
                (show u.ctx_uvar_head)
                (show sol)
                (show g)
          )
          else (
            proc_guard' false "guard for implicit" env guard (Some sc) u.ctx_uvar_range ;!
            mark_uvar_as_already_checked u;
            ret ()
          )

        | Inr failed ->
          fail3 "Could not typecheck unifier solved implicit %s to %s because %s"
            (show u.ctx_uvar_head)
            (show sol)
            (Core.print_error failed)
  in
  if env.phase1 //phase1 is untrusted
  then ret ()
  else uvs |> iter_tac aux

//
// When calling Rel for t1 `rel` t2, caller can choose to tc
//   implicits solved during this unification
// With side argument they can control, which side args to check
// E.g. do_match will choose only Right,
//   since it fails if some uvar on the left is instantiated
//
type check_unifier_solved_implicits_side =
  | Check_none
  | Check_left_only
  | Check_right_only
  | Check_both

let __do_unify_wflags
  (dbg:bool)
  (allow_guards:bool)
  (must_tot:bool)
  (check_side:check_unifier_solved_implicits_side)
  (env:env) (t1:term) (t2:term)
  : tac (option guard_t) =
    if dbg then
      BU.print2 "%%%%%%%%do_unify %s =? %s\n" (show t1)
                                              (show t2);

    let all_uvars =
      (match check_side with
       | Check_none -> empty ()
       | Check_left_only -> Free.uvars t1
       | Check_right_only -> Free.uvars t2
       | Check_both -> union (Free.uvars t1) (Free.uvars t2))
      |> elems in

    match!
      catch (//restore UF graph in case anything fails
        bind (trytac cur_goal) (fun gopt ->
        try
          let res =
            if allow_guards
            then Rel.try_teq true env t1 t2
            else Rel.teq_nosmt env t1 t2
          in
          if dbg then
            BU.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                              (FStarC.Common.string_of_option (Rel.guard_to_string env) res)
                              (show t1)
                              (show t2);

          match res with
          | None ->
            ret None
          | Some g ->
            tc_unifier_solved_implicits env must_tot allow_guards all_uvars;!
            add_implicits (Listlike.to_list g.implicits);!
            ret (Some g)

        with | Errors.Error (_, msg, r, _) -> begin
                            mlog (fun () -> BU.print2 ">> do_unify error, (%s) at (%s)\n"
                            (Errors.rendermsg msg) (show r)) (fun _ ->
                            ret None)
               end
        )
      )
    with
    | Inl exn -> traise exn
    | Inr v -> ret v

(* Just a wrapper over __do_unify_wflags to better debug *)
let __do_unify
  (allow_guards:bool)
  (must_tot:bool)
  (check_side:check_unifier_solved_implicits_side)
  (env:env) (t1:term) (t2:term)
  : tac (option guard_t) =
  bind idtac (fun () ->
  if !dbg_TacUnify then begin
    Options.push ();
    let _ = Options.set_options "--debug Rel,RelCheck" in
    ()
  end;
  bind (__do_unify_wflags !dbg_TacUnify allow_guards must_tot check_side env t1 t2) (fun r ->
  if !dbg_TacUnify then Options.pop ();
  ret r))

(* SMT-free unification. *)
let do_unify_aux
  (must_tot:bool)
  (check_side:check_unifier_solved_implicits_side)
  (env:env) (t1:term) (t2:term)
  : tac bool =
  bind (__do_unify false must_tot check_side env t1 t2) (function
  | None -> ret false
  | Some g ->
    (* g has to be trivial and we have already added its implicits *)
    if not (Env.is_trivial_guard_formula g) then
      failwith "internal error: do_unify: guard is not trivial";
    ret true
  )

let do_unify (must_tot:bool) (env:env) (t1:term) (t2:term) : tac bool =
  do_unify_aux must_tot Check_both env t1 t2

let do_unify_maybe_guards (allow_guards:bool) (must_tot:bool)
  (env:env) (t1:term) (t2:term)
  : tac (option guard_t) =
  __do_unify allow_guards must_tot Check_both env t1 t2

(* Does t1 match t2? That is, do they unify without instantiating/changing t1? *)
let do_match (must_tot:bool) (env:Env.env) (t1:term) (t2:term) : tac bool =
    bind (mk_tac (fun ps -> let tx = UF.new_transaction () in
                            Success (tx, ps))) (fun tx ->
    let uvs1 = SF.uvars_uncached t1 in
    bind (do_unify_aux must_tot Check_right_only env t1 t2) (fun r ->
    if r then begin
        let uvs2 = SF.uvars_uncached t1 in
        if not (equal uvs1 uvs2)
        then (UF.rollback tx; ret false)
        else ret true
    end
    else ret false
    ))

(* This is a bandaid. It's similar to do_match but checks that the
LHS of the equality in [t1] is not instantiated, but the RHS might be.
It is a pain to expose the whole logic to tactics, so we just do it
here for now. *)
let do_match_on_lhs (must_tot:bool) (env:Env.env) (t1:term) (t2:term) : tac bool =
    bind (mk_tac (fun ps -> let tx = UF.new_transaction () in
                            Success (tx, ps))) (fun tx ->
    match destruct_eq env t1 with
    | None -> fail "do_match_on_lhs: not an eq"
    | Some (lhs, _) ->
    let uvs1 = SF.uvars_uncached lhs in
    bind (do_unify_aux must_tot Check_right_only env t1 t2) (fun r ->
    if r then begin
        let uvs2 = SF.uvars_uncached lhs in
        if not (equal uvs1 uvs2)
        then (UF.rollback tx; ret false)
        else ret true
    end
    else ret false
    ))

(*
   set_solution:

     Sometimes the witness of a goal is solved by
     using a low-level assignment of the unification variable
     provided by set_solution.

     The general discipline is that when a trusted primitive tactic
     constructs a term to solve the current goal, then it should be
     able to just do a set_solution.

     OTOH, if it's a user-provided term to solve the goal, then trysolve is safer

     Note, set_solution is not just an optimization. In cases like `intro`
     it is actually important to get the right shape of goal. See the comment there.
*)
let set_solution goal solution : tac unit =
    match FStarC.Syntax.Unionfind.find goal.goal_ctx_uvar.ctx_uvar_head with
    | Some _ ->
      fail (BU.format1 "Goal %s is already solved" (goal_to_string_verbose goal))
    | None ->
      FStarC.Syntax.Unionfind.change goal.goal_ctx_uvar.ctx_uvar_head solution;
      mark_goal_implicit_already_checked goal;
      ret ()

let trysolve (goal : goal) (solution : term) : tac bool =
  let must_tot = true in
  do_unify must_tot (goal_env goal) solution (goal_witness goal)

let solve (goal : goal) (solution : term) : tac unit =
    let e = goal_env goal in
    mlog (fun () -> BU.print2 "solve %s := %s\n" (show (goal_witness goal))
                                                 (show solution)) (fun () ->
    bind (trysolve goal solution) (fun b ->
    if b
    then bind dismiss (fun () -> remove_solved_goals)
    else fail (BU.format3 "%s does not solve %s : %s"
              (tts (goal_env goal) solution)
              (tts (goal_env goal) (goal_witness goal))
              (tts (goal_env goal) (goal_type goal)))))


let solve' (goal : goal) (solution : term) : tac unit =
    bind (set_solution goal solution) (fun () ->
    bind dismiss (fun () ->
    remove_solved_goals))

//Any function that directly calls these utilities is also trusted
//End: Trusted utilities
////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////
(* Some utilities on goals *)
let is_true t =
    let t = U.unascribe t in
    match U.un_squash t with
    | Some t' ->
        let t' = U.unascribe t' in
        begin match (SS.compress t').n with
        | Tm_fvar fv -> S.fv_eq_lid fv PC.true_lid
        | _ -> false
        end
    | _ -> false

let is_false t =
    match U.un_squash t with
    | Some t' ->
        begin match (SS.compress t').n with
        | Tm_fvar fv -> S.fv_eq_lid fv PC.false_lid
        | _ -> false
        end
    | _ -> false
////////////////////////////////////////////////////////////////////


let tadmit_t (t:term) : tac unit = wrap_err "tadmit_t" <|
    bind get (fun ps ->
    bind cur_goal (fun g ->
    // should somehow taint the state instead of just printing a warning
    Err.log_issue (goal_type g) Errors.Warning_TacAdmit
      (BU.format1 "Tactics admitted goal <%s>\n\n" (goal_to_string "" None ps g));
    solve' g t))

let fresh () : tac Z.t =
    bind get (fun ps ->
    let n = ps.freshness in
    let ps = { ps with freshness = n + 1 } in
    bind (set ps) (fun () ->
    ret (Z.of_int_fs n)))

let curms () : tac Z.t =
    ret (BU.get_time_of_day_ms () |> Z.of_int_fs)

(* Annoying duplication here *)
let __tc (e : env) (t : term) : tac (term & typ & guard_t) =
    bind get (fun ps ->
    mlog (fun () -> BU.print1 "Tac> __tc(%s)\n" (show t)) (fun () ->
    let e = {e with uvar_subtyping=false} in
    try ret (TcTerm.typeof_tot_or_gtot_term e t true)
    with | Errors.Error (_, msg, _, _) -> begin
           fail3 "Cannot type (1) %s in context (%s). Error = (%s)" (tts e t)
                                                  (Env.all_binders e |> show)
                                                  (Errors.rendermsg msg) // FIXME
           end))

let __tc_ghost (e : env) (t : term) : tac (term & typ & guard_t) =
    bind get (fun ps ->
    mlog (fun () -> BU.print1 "Tac> __tc_ghost(%s)\n" (show t)) (fun () ->
    let e = {e with uvar_subtyping=false} in
    let e = {e with letrecs=[]} in
    try let t, lc, g = TcTerm.tc_tot_or_gtot_term e t in
        ret (t, lc.res_typ, g)
    with | Errors.Error (_, msg, _ ,_) -> begin
           fail3 "Cannot type (2) %s in context (%s). Error = (%s)" (tts e t)
                                                  (Env.all_binders e |> show)
                                                  (Errors.rendermsg msg) // FIXME
           end))

let __tc_lax (e : env) (t : term) : tac (term & lcomp & guard_t) =
    bind get (fun ps ->
    mlog (fun () -> BU.print2 "Tac> __tc_lax(%s)(Context:%s)\n"
                           (show t)
                           (Env.all_binders e |> show)) (fun () ->
    let e = {e with uvar_subtyping=false} in
    let e = {e with admit = true} in
    let e = {e with letrecs=[]} in
    try ret (TcTerm.tc_term e t)
    with | Errors.Error (_, msg, _, _) -> begin
           fail3 "Cannot type (3) %s in context (%s). Error = (%s)" (tts e t)
                                                  (Env.all_binders e |> show)
                                                  (Errors.rendermsg msg) // FIXME
           end))

let tcc (e : env) (t : term) : tac comp = wrap_err "tcc" <|
    bind (__tc_lax e t) (fun (_, lc, _) ->
    (* Why lax? What about the guard? It doesn't matter! tc is only
     * a way for metaprograms to query the typechecker, but
     * the result has no effect on the proofstate and nor is it
     * taken for a fact that the typing is correct. *)
    ret (TcComm.lcomp_comp lc |> fst)  //dropping the guard from lcomp_comp too!
    )

let tc (e : env) (t : term) : tac typ = wrap_err "tc" <|
    bind (tcc e t) (fun c -> ret (U.comp_result c))

let divide (n:Z.t) (l : tac 'a) (r : tac 'b) : tac ('a & 'b) =
    bind get (fun p ->
    bind (try ret (List.splitAt (Z.to_int_fs n) p.goals) with | _ -> fail "divide: not enough goals") (fun (lgs, rgs) ->
    let lp = { p with goals = lgs; smt_goals = [] } in
    bind (set lp) (fun _ ->
    bind l        (fun a ->
    bind get      (fun lp' ->
    let rp = { lp' with goals = rgs; smt_goals = [] } in
    bind (set rp) (fun _ ->
    bind r        (fun b ->
    bind get      (fun rp' ->
    let p' = { rp' with goals=lp'.goals @ rp'.goals; smt_goals = lp'.smt_goals @ rp'.smt_goals @ p.smt_goals } in
    bind (set p') (fun _ ->
    bind remove_solved_goals (fun () ->
    ret (a, b)))))))))))

(* focus: runs f on the current goal only, and then restores all the goals *)
(* There is a user defined version as well, we just use this one internally, but can't mark it as private *)
let focus (f:tac 'a) : tac 'a =
    bind (divide Z.one f idtac) (fun (a, ()) -> ret a)

(* Applies t to each of the current goals
      fails if t fails on any of the goals
      collects each result in the output list *)
let rec map (tau:tac 'a): tac (list 'a) =
        bind get (fun p ->
        match p.goals with
        | [] -> ret []
        | _::_ ->
            bind (divide Z.one tau (map tau)) (fun (h,t) -> ret (h :: t))
        )

(* Applies t1 to the current head goal
   And t2 to all the the sub-goals produced by t1

   Collects the resulting goals of t2 along with the initial auxiliary goals
 *)
let seq (t1:tac unit) (t2:tac unit) : tac unit =
    focus (
        bind t1 (fun _ ->
        bind (map t2) (fun _ -> ret ()))
    )

let should_check_goal_uvar (g:goal) = U.ctx_uvar_should_check g.goal_ctx_uvar
let goal_typedness_deps (g:goal) = U.ctx_uvar_typedness_deps g.goal_ctx_uvar

let bnorm_and_replace g = replace_cur (bnorm_goal g)

let arrow_one (env:Env.env) (t:term) =
  match U.arrow_one_ln t with
  | None -> None
  | Some (b, c) ->
    let env, [b], c = FStarC.TypeChecker.Core.open_binders_in_comp env [b] c in
    Some (env, b, c)

(*
  [intro]:

  Initial goal: G |- ?u : (t -> t')

  Now we do an `intro`:

  Next goal:  `G, x:t |- ?v : t'`

  with `?u := (fun (x:t) -> ?v @ [NM(x, 0)])`
*)
let intro () : tac binder = wrap_err "intro" <| (
    let! goal = cur_goal in
    match arrow_one (goal_env goal) (whnf (goal_env goal) (goal_type goal)) with
    | Some (env', b, c) ->
        if not (U.is_total_comp c)
        then fail "Codomain is effectful"
        else let typ' = U.comp_result c in
             //BU.print1 "[intro]: current goal is %s" (goal_to_string goal);
             //BU.print1 "[intro]: current goal witness is %s" (show (goal_witness goal));
             //BU.print1 "[intro]: with goal type %s" (show (goal_type goal));
             //BU.print2 "[intro]: with binder = %s, new goal = %s"
             //         (Print.binders_to_string ", " [b])
             //         (show typ');
             let! body, ctx_uvar =
               new_uvar "intro" env' typ'
                        (Some (should_check_goal_uvar goal))
                        (goal_typedness_deps goal)
                        (rangeof goal) in
             let sol = U.abs [b] body (Some (U.residual_comp_of_comp c)) in
             //BU.print1 "[intro]: solution is %s"
             //           (show sol);
             //BU.print1 "[intro]: old goal is %s" (goal_to_string goal);
             //BU.print1 "[intro]: new goal is %s"
             //           (show ctx_uvar);
             //ignore (FStarC.Options.set_options "--debug Rel");
              (* Suppose if instead of simply assigning `?u` to the lambda term on
                the RHS, we tried to unify `?u` with the `(fun (x:t) -> ?v @ [NM(x, 0)])`.

                Then, this would defeat the purpose of the delayed substitution, since
                the unification engine would solve it by doing something like

                  `(fun (y:t) ->  ?u y)  ~ (fun (x:t) -> ?v @ [NM(x, 0)])`

                And then solving

                  `?u z ~ ?v @ [NT(x, z)]`

                which would then proceed by solving `?v` to `?w z` and then unifying
                `?u` and `?w`.

                I.e., this immediately destroys the nice shape of the next goal.
             *)
             set_solution goal sol ;!
             let g = mk_goal env' ctx_uvar goal.opts goal.is_guard goal.label in
             bnorm_and_replace g ;!
             ret b
    | None ->
        fail1 "goal is not an arrow (%s)" (tts (goal_env goal) (goal_type goal))
    )


// TODO: missing: precedes clause, and somehow disabling fixpoints only as needed
let intro_rec () : tac (binder & binder) =
    let! goal = cur_goal in
    BU.print_string "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
    BU.print_string "WARNING (intro_rec): proceed at your own risk...\n";
    match arrow_one (goal_env goal) (whnf (goal_env goal) (goal_type goal)) with
    | Some (env', b, c) ->
        if not (U.is_total_comp c)
        then fail "Codomain is effectful"
        else let bv = gen_bv "__recf" None (goal_type goal) in
             let! u, ctx_uvar_u =
                  new_uvar "intro_rec" env'
                    (U.comp_result c)
                    (Some (should_check_goal_uvar goal))
                    (goal_typedness_deps goal)
                    (rangeof goal) in
             let lb = U.mk_letbinding (Inl bv) [] (goal_type goal) PC.effect_Tot_lid (U.abs [b] u None) [] Range.dummyRange in
             let body = S.bv_to_name bv in
             let lbs, body = SS.close_let_rec [lb] body in
             let tm = mk (Tm_let {lbs=(true, lbs); body}) (goal_witness goal).pos in
             set_solution goal tm ;!
             bnorm_and_replace { goal with goal_ctx_uvar=ctx_uvar_u} ;!
             ret (S.mk_binder bv, b)
    | None ->
        fail1 "intro_rec: goal is not an arrow (%s)" (tts (goal_env goal) (goal_type goal))

let norm (s : list NormSteps.norm_step) : tac unit =
    let! goal = cur_goal in
    if_verbose (fun () -> BU.print1 "norm: witness = %s\n" (show (goal_witness goal))) ;!
    // Translate to actual normalizer steps
    let steps = [Env.Reify; Env.DontUnfoldAttr [PC.tac_opaque_attr]]@(Cfg.translate_norm_steps s) in
    //let w = normalize steps (goal_env goal) (goal_witness goal) in
    let t = normalize steps (goal_env goal) (goal_type goal) in
    replace_cur (goal_with_type goal t)


let norm_term_env (e : env) (s : list NormSteps.norm_step) (t : term) : tac term = wrap_err "norm_term" <| (
    let! ps = get in
    if_verbose (fun () -> BU.print1 "norm_term_env: t = %s\n" (show t)) ;!
    // only for elaborating lifts and all that, we don't care if it's actually well-typed
    let! t, _, _ = __tc_lax e t in
    let steps = [Env.Reify; Env.DontUnfoldAttr [PC.tac_opaque_attr]]@(Cfg.translate_norm_steps s) in
    let t = normalize steps ps.main_context t in
    if_verbose (fun () -> BU.print1 "norm_term_env: t' = %s\n" (show t)) ;!
    ret t
    )


let refine_intro () : tac unit = wrap_err "refine_intro" <| (
    let! g = cur_goal in
    match Rel.base_and_refinement (goal_env g) (goal_type g) with
    | _, None -> fail "not a refinement"
    | t, Some (bv, phi) ->
      //Mark goal as untyped, since we're adding its refinement as a separate goal
      mark_goal_implicit_already_checked g;
      let g1 = goal_with_type g t in
      let bv, phi =
        let bvs, phi = SS.open_term [S.mk_binder bv] phi in
        (List.hd bvs).binder_bv, phi
      in
      let! g2 = mk_irrelevant_goal "refine_intro refinement" (goal_env g)
                    (SS.subst [S.NT (bv, (goal_witness g))] phi)
                    (Some (should_check_goal_uvar g))
                    (rangeof g)
                    g.opts
                    g.label in
      dismiss ;!
      add_goals [g1;g2]
    )

let __exact_now set_expected_typ (t:term) : tac unit =
    let! goal = cur_goal in
    let env = if set_expected_typ
              then Env.set_expected_typ (goal_env goal) (goal_type goal)
              else (goal_env goal)
    in
    let! t, typ, guard = __tc env t in
    if_verbose (fun () -> BU.print2 "__exact_now: got type %s\n__exact_now: and guard %s\n"
                                                     (show typ)
                                                     (Rel.guard_to_string (goal_env goal) guard)) ;!
    proc_guard "__exact typing" (goal_env goal) guard (Some (should_check_goal_uvar goal)) (rangeof goal) ;!
    if_verbose (fun () -> BU.print2 "__exact_now: unifying %s and %s\n" (show typ)
                                                                  (show (goal_type goal))) ;!
    let! b = do_unify true (goal_env goal) typ (goal_type goal) in
    if b
    then ( // do unify succeeded with a trivial guard; so the goal is solved and we don't have to check it again
      mark_goal_implicit_already_checked goal;
      solve goal t
    )
    else
      let typ, goalt = TypeChecker.Err.print_discrepancy (tts (goal_env goal)) typ (goal_type goal) in
      fail4 "%s : %s does not exactly solve the goal %s (witness = %s)"
                    (tts (goal_env goal) t)
                    typ
                    goalt
                    (tts (goal_env goal) (goal_witness goal))

let t_exact try_refine set_expected_typ tm : tac unit = wrap_err "exact" <| (
    if_verbose (fun () -> BU.print1 "t_exact: tm = %s\n" (show tm)) ;!
    match! catch (__exact_now set_expected_typ tm) with
    | Inr r -> ret r
    | Inl e when not (try_refine) -> traise e
    | Inl e ->
      if_verbose (fun () -> BU.print_string "__exact_now failed, trying refine...\n") ;!
      match! catch (norm [NormSteps.Delta] ;! refine_intro () ;! __exact_now set_expected_typ tm) with
      | Inr r ->
        if_verbose (fun () -> BU.print_string "__exact_now: failed after refining too\n") ;!
        ret r
      | Inl _ ->
        if_verbose (fun () -> BU.print_string "__exact_now: was not a refinement\n") ;!
        traise e)

(* Can t1 unify t2 if it's applied to arguments? If so return uvars for them *)
(* NB: Result is reversed, which helps so we use fold_right instead of fold_left *)
let try_unify_by_application (should_check:option should_check_uvar)
                             (only_match:bool)
                             (e : env)
                             (ty1 : term)
                             (ty2 : term)
                             (rng:Range.range)
   : tac (list (term & aqual & ctx_uvar))
   = let f = if only_match then do_match else do_unify in
     let must_tot = true in
     let rec aux (acc : list (term & aqual & ctx_uvar))
                 (typedness_deps : list ctx_uvar) //map proj_3 acc
                 (ty1:term)
        : tac (list (term & aqual & ctx_uvar))
        = match! f must_tot e ty2 ty1 with
          | true -> ret acc (* Done! *)
          | false ->
            (* Not a match, try instantiating the first type by application *)
            match U.arrow_one ty1 with
            | None ->
              fail2 "Could not instantiate, %s to %s" (tts e ty1) (tts e ty2)

            | Some (b, c) ->
              if not (U.is_total_comp c) then fail "Codomain is effectful" else
              let! uvt, uv = new_uvar "apply arg" e b.binder_bv.sort should_check typedness_deps rng in
              if_verbose (fun () -> BU.print1 "t_apply: generated uvar %s\n" (show uv)) ;!
              let typ = U.comp_result c in
              let typ' = SS.subst [S.NT (b.binder_bv, uvt)] typ in
              aux ((uvt, U.aqual_of_binder b, uv)::acc) (uv::typedness_deps) typ'
     in
     aux [] [] ty1

//
// Goals for implicits created during apply
//
let apply_implicits_as_goals
    (env:Env.env)
    (gl:option goal)
    (imps:list (term & ctx_uvar))
  : tac (list (list goal)) =

  let one_implicit_as_goal (term, ctx_uvar) =
    let hd, _ = U.head_and_args term in
    match (SS.compress hd).n with
    | Tm_uvar (ctx_uvar, _) ->
      let gl =
        match gl with
        | None ->  mk_goal env ctx_uvar (FStarC.Options.peek()) true "goal for unsolved implicit"
        | Some gl -> { gl with goal_ctx_uvar = ctx_uvar } in  //TODO: AR: what's happening here?
      let gl = bnorm_goal gl in
      ret [gl]
    | _ ->
      //
      // This implicits has already been solved
      // We would have typechecked its solution already,
      //   just after the Rel call
      //
      ret []
  in
  imps |> mapM one_implicit_as_goal

// uopt: Don't add goals for implicits that appear free in posterior goals.
// This is very handy for users, allowing to turn
//
// |- a = c
//
// by applying transivity to
//
// |- a = ?u
// |- ?u = c
//
// without asking for |- ?u : Type first, which will most likely be instantiated when
// solving any of these two goals. In any case, if ?u is not solved, we will later fail.
// TODO: this should probably be made into a user tactic
let t_apply (uopt:bool) (only_match:bool) (tc_resolved_uvars:bool) (tm:term) : tac unit = wrap_err "apply" <| (
    let tc_resolved_uvars = true in
    if_verbose
      (fun () -> BU.print4 "t_apply: uopt %s, only_match %s, tc_resolved_uvars %s, tm = %s\n"
                   (show uopt)
                   (show only_match)
                   (show tc_resolved_uvars)
                   (show tm)) ;!
    let! ps = get in
    let! goal = cur_goal in
    let e = goal_env goal in
    let should_check = should_check_goal_uvar goal in
    Tactics.Monad.register_goal goal;
    let! tm, typ, guard = __tc e tm in
    if_verbose
      (fun () -> BU.print5 "t_apply: tm = %s\nt_apply: goal = %s\nenv.gamma=%s\ntyp=%s\nguard=%s\n"
                        (show tm)
                        (goal_to_string_verbose goal)
                        (show e.gamma)
                        (show typ)
                        (Rel.guard_to_string e guard)) ;!
    // Focus helps keep the goal order
    let typ = bnorm e typ in
    let! uvs = try_unify_by_application (Some should_check) only_match e typ (goal_type goal) (rangeof goal) in
    if_verbose
      (fun () -> BU.print1 "t_apply: found args = %s\n"
                        (FStarC.Common.string_of_list (fun (t, _, _) -> show t) uvs)) ;!
    let w = List.fold_right (fun (uvt, q, _) w -> U.mk_app w [(uvt, q)]) uvs tm in
    let uvset =
      List.fold_right
        (fun (_, _, uv) s -> union s (SF.uvars (U.ctx_uvar_typ uv)))
        uvs
        (empty ())
    in
    let free_in_some_goal uv = mem uv uvset in
    solve' goal w ;!
    //
    //process uvs
    //first, if some of them are solved already, perhaps during unification,
    //  typecheck them if tc_resolved_uvars is on
    //then, if uopt is on, filter out those that appear in other goals
    //add the rest as goals
    //
    let uvt_uv_l = uvs |> List.map (fun (uvt, _q, uv) -> (uvt, uv)) in
    let! sub_goals =
      apply_implicits_as_goals e (Some goal) uvt_uv_l in
    let sub_goals = List.flatten sub_goals
                  |> List.filter (fun g ->
                                  //if uopt is on, we don't keep uvars that
                                  //  appear in some other goals
                                  not (uopt && free_in_some_goal g.goal_ctx_uvar))
                   |> List.map bnorm_goal
                   |> List.rev in
    add_goals sub_goals ;!
    proc_guard "apply guard" e guard (Some should_check) (rangeof goal)
  )

// returns pre and post
let lemma_or_sq (c : comp) : option (term & term) =
    let eff_name, res, args = U.comp_eff_name_res_and_args c in
    if lid_equals eff_name PC.effect_Lemma_lid then
        let pre, post = match args with
                        | pre::post::_ -> fst pre, fst post
                        | _ -> failwith "apply_lemma: impossible: not a lemma"
        in
        // Lemma post is thunked
        let post = U.mk_app post [S.as_arg U.exp_unit] in
        Some (pre, post)
    else if U.is_pure_effect eff_name
         || U.is_ghost_effect eff_name then
        map_opt (U.un_squash res) (fun post -> (U.t_true, post))
    else
        None

let rec fold_left (f : ('a -> 'b -> tac 'b)) (e : 'b) (xs : list 'a) : tac 'b =
    match xs with
    | [] -> ret e
    | x::xs -> bind (f x e) (fun e' -> fold_left f e' xs)

let t_apply_lemma (noinst:bool) (noinst_lhs:bool)
                  (tm:term) : tac unit = wrap_err "apply_lemma" <| focus (
    let! ps = get in
    if_verbose (fun () -> BU.print1 "apply_lemma: tm = %s\n" (show tm)) ;!
    let is_unit_t t =
      match (SS.compress t).n with
      | Tm_fvar fv when S.fv_eq_lid fv PC.unit_lid -> true
      | _ -> false
    in
    let! goal = cur_goal in
    let env = goal_env goal in
    Tactics.Monad.register_goal goal;
    let! tm, t, guard = __tc env tm in
    let bs, comp = U.arrow_formals_comp t in
    match lemma_or_sq comp with
    | None -> fail "not a lemma or squashed function"
    | Some (pre, post) ->
      let! uvs, _, implicits, subst =
        fold_left
          (fun ({binder_bv=b;binder_qual=aq}) (uvs, deps, imps, subst) ->
               let b_t = SS.subst subst b.sort in
               if is_unit_t b_t
               then
                   // Simplification: if the argument is simply unit, then don't ask for it
                   ret <| ((U.exp_unit, aq)::uvs, deps, imps, S.NT(b, U.exp_unit)::subst)
               else
                   let! t, u = new_uvar "apply_lemma" env b_t
                     (goal
                      |> should_check_goal_uvar
                      |> (function | Strict -> Allow_ghost "apply lemma uvar"
                                  | x -> x)
                      |> Some)
                     deps
                     (rangeof goal) in
                   if Debug.medium () || !dbg_2635
                   then
                     BU.print2 "Apply lemma created a new uvar %s while applying %s\n"
                       (show u)
                       (show tm);
                   ret ((t, aq)::uvs, u::deps, (t, u)::imps, S.NT(b, t)::subst))
          ([], [], [], [])
          bs
      in
      let implicits = List.rev implicits in
      let uvs = List.rev uvs in
      let pre  = SS.subst subst pre in
      let post = SS.subst subst post in
      let post_u = env.universe_of env post in
      let cmp_func =
          if noinst then do_match
          else if noinst_lhs then do_match_on_lhs
          else do_unify
      in
      let! b =
        let must_tot = false in
        cmp_func must_tot env (goal_type goal) (U.mk_squash post_u post) in
      if not b
      then (
        let post, goalt = TypeChecker.Err.print_discrepancy (tts env)
                                                            (U.mk_squash post_u post)
                                                            (goal_type goal) in
        fail3 "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                            (tts env tm) post goalt
      )
      else (
        // We solve with (), we don't care about the witness if applying a lemma
        let goal_sc = should_check_goal_uvar goal in
        solve' goal U.exp_unit ;!
        let is_free_uvar uv t =
            let free_uvars = List.map (fun x -> x.ctx_uvar_head) (elems (SF.uvars t)) in
            List.existsML (fun u -> UF.equiv u uv) free_uvars
        in
        let appears uv goals = List.existsML (fun g' -> is_free_uvar uv (goal_type g')) goals in
        let checkone t goals =
            let hd, _ = U.head_and_args t in
            begin match hd.n with
            | Tm_uvar (uv, _) -> appears uv.ctx_uvar_head goals
            | _ -> false
            end
        in
        let must_tot = false in
        let! sub_goals =
             apply_implicits_as_goals env (Some goal) implicits in
        let sub_goals = List.flatten sub_goals in
        // Optimization: if a uvar appears in a later goal, don't ask for it, since
        // it will be instantiated later. It is tracked anyway in ps.implicits
        let rec filter' (f : 'a -> list 'a -> bool) (xs : list 'a) : list 'a =
             match xs with
             | [] -> []
             | x::xs -> if f x xs then x::(filter' f xs) else filter' f xs
        in
        let sub_goals = filter' (fun g goals -> not (checkone (goal_witness g) goals)) sub_goals in
        proc_guard "apply_lemma guard" env guard (Some goal_sc) (rangeof goal) ;!
        let pre_u = env.universe_of env pre in
        (match (Rel.simplify_guard env (Env.guard_of_guard_formula (NonTrivial pre))).guard_f with
         | Trivial -> ret ()
         | NonTrivial _ -> add_irrelevant_goal goal "apply_lemma precondition" env pre (Some goal_sc)) ;!//AR: should we use the normalized pre instead?
        add_goals sub_goals
      )
    )

let split_env (bvar : bv) (e : env) : option (env & bv & list bv) =
    let rec aux e =
        match Env.pop_bv e with
        | None -> None
        | Some (bv', e') ->
            if S.bv_eq bvar bv'
            then Some (e', bv', [])
            else map_opt (aux e') (fun (e'', bv, bvs) -> (e'', bv, bv'::bvs ))
    in
    map_opt (aux e) (fun (e', bv, bvs) -> (e', bv, List.rev bvs))

let subst_goal (b1 : bv) (b2 : bv) (g:goal) : tac (option (bv & goal)) =
    match split_env b1 (goal_env g) with
    | Some (e0, b1, bvs) ->
        let bs = List.map S.mk_binder (b1::bvs) in

        let t = goal_type g in

        (* Close the binders and t *)
        let bs', t' = SS.close_binders bs, SS.close bs t in

        (* Replace b1 (the head) by b2 *)
        let bs' = S.mk_binder b2 :: List.tail bs' in

        (* Re-open, all done for renaming *)
        let new_env, bs'', t'' = Core.open_binders_in_term e0 bs' t' in

        // (* b2 has been freshened *)
        let b2 = (List.hd bs'').binder_bv in

        // (* Make a new goal in the new env (with new binders) *)
        let! uvt, uv = new_uvar "subst_goal" new_env t''
                               (Some (should_check_goal_uvar g))
                               (goal_typedness_deps g)
                               (rangeof g) in

        let goal' = mk_goal new_env uv g.opts g.is_guard g.label in

        (* Solve the old goal with an application of the new witness *)
        let sol = U.mk_app (U.abs bs'' uvt None)
                           (List.map (fun ({binder_bv=bv;binder_qual=q}) -> S.as_arg (S.bv_to_name bv)) bs) in

        set_solution g sol ;!

        ret (Some (b2, goal'))

    | None ->
        ret None

let rewrite (h:binder) : tac unit = wrap_err "rewrite" <| (
    let! goal = cur_goal in
    let bv = h.binder_bv in
    if_verbose (fun _ -> BU.print2 "+++Rewrite %s : %s\n" (show bv) (show bv.sort)) ;!
    match split_env bv (goal_env goal) with
    | None -> fail "binder not found in environment"
    | Some (e0, bv, bvs) ->
      begin
      match destruct_eq e0 bv.sort with
      | Some (x, e) ->
        begin
        match (SS.compress x).n with
        | Tm_name x ->
          let s = [NT(x, e)] in

          (* See subst_goal for an explanation *)
          let t = goal_type goal in
          let bs = List.map S.mk_binder bvs in

          let bs', t' = SS.close_binders bs, SS.close bs t in
          let bs', t' = SS.subst_binders s bs', SS.subst s t' in
          let e0 = Env.push_bvs e0 [bv] in
          let new_env, bs'', t'' = Core.open_binders_in_term e0 bs' t' in

          let! uvt, uv =
               new_uvar "rewrite" new_env t''
                           (Some (should_check_goal_uvar goal))
                           (goal_typedness_deps goal)
                           (rangeof goal)
          in
          let goal' = mk_goal new_env uv goal.opts goal.is_guard goal.label in
          let sol = U.mk_app (U.abs bs'' uvt None)
                             (List.map (fun ({binder_bv=bv}) -> S.as_arg (S.bv_to_name bv)) bs) in

          (* See comment in subst_goal *)
          set_solution goal sol ;!
          replace_cur goal'

        | _ ->
          fail "Not an equality hypothesis with a variable on the LHS"
        end
      | _ -> fail "Not an equality hypothesis"
      end
    )

let rename_to (b : binder) (s : string) : tac binder = wrap_err "rename_to" <| (
    let! goal = cur_goal in
    let bv = b.binder_bv in
    let bv' = freshen_bv ({ bv with ppname = mk_ident (s, (range_of_id bv.ppname)) }) in
    match! subst_goal bv bv' goal with
    | None -> fail "binder not found in environment"
    | Some (bv',  goal) ->
      replace_cur goal ;!
      ret {b with binder_bv=bv'}
    )

let binder_retype (b : binder) : tac unit = wrap_err "binder_retype" <| (
    let! goal = cur_goal in
    let bv = b.binder_bv in
    match split_env bv (goal_env goal) with
    | None -> fail "binder is not present in environment"
    | Some (e0, bv, bvs) ->
      let (ty, u) = U.type_u () in
      let goal_sc = should_check_goal_uvar goal in
      let! t', u_t' =
           new_uvar "binder_retype" e0 ty
                    (Some goal_sc)
                    (goal_typedness_deps goal)
                    (rangeof goal)
      in
      let bv'' = {bv with sort = t'} in
      let s = [S.NT (bv, S.bv_to_name bv'')] in
      let bvs = List.map (fun b -> { b with sort = SS.subst s b.sort }) bvs in
      let env' = Env.push_bvs e0 (bv''::bvs) in
      dismiss ;!
      let new_goal =
          goal_with_type
                (goal_with_env goal env')
                (SS.subst s (goal_type goal))
      in
      add_goals [new_goal] ;!
      add_irrelevant_goal goal "binder_retype equation" e0
                          (U.mk_eq2 (U_succ u) ty bv.sort t')
                          (Some goal_sc)
    )

(* TODO: move to bv *)
let norm_binder_type (s : list NormSteps.norm_step) (b : binder) : tac unit = wrap_err "norm_binder_type" <| (
    let! goal = cur_goal in
    let bv = b.binder_bv in
    match split_env bv (goal_env goal) with
    | None -> fail "binder is not present in environment"
    | Some (e0, bv, bvs) ->
      let steps = [Env.Reify; Env.DontUnfoldAttr [PC.tac_opaque_attr]]@(Cfg.translate_norm_steps s) in
      let sort' = normalize steps e0 bv.sort in
      let bv' = { bv with sort = sort' } in
      let env' = Env.push_bvs e0 (bv'::bvs) in
      replace_cur (goal_with_env goal env')
    )

let revert () : tac unit =
    let! goal = cur_goal in
    match Env.pop_bv (goal_env goal) with
    | None -> fail "Cannot revert; empty context"
    | Some (x, env') ->
      let typ' = U.arrow [S.mk_binder x] (mk_Total (goal_type goal)) in
      let! r, u_r =
        new_uvar "revert" env' typ'
                 (Some (should_check_goal_uvar goal))
                 (goal_typedness_deps goal)
                 (rangeof goal) in
      set_solution goal (S.mk_Tm_app r [S.as_arg (S.bv_to_name x)] (goal_type goal).pos) ;!
      let g = mk_goal env' u_r goal.opts goal.is_guard goal.label in
      replace_cur g

let free_in bv t = mem bv (SF.names t)

let clear (b : binder) : tac unit =
    let bv = b.binder_bv in
    let! goal = cur_goal in
    if_verbose (fun () -> BU.print2 "Clear of (%s), env has %s binders\n"
                        (show b)
                        (Env.all_binders (goal_env goal) |> List.length |> show)) ;!
    match split_env bv (goal_env goal) with
    | None -> fail "Cannot clear; binder not in environment"
    | Some (e', bv, bvs) ->
      let rec check bvs =
          match bvs with
          | [] -> ret ()
          | bv'::bvs ->
            if free_in bv bv'.sort
            then fail (BU.format1 "Cannot clear; binder present in the type of %s"
                                    (show bv'))
            else check bvs
      in
      if free_in bv (goal_type goal) then
         fail "Cannot clear; binder present in goal"
      else (
        check bvs ;!
        let env' = Env.push_bvs e' bvs in
        let! ut, uvar_ut =
             new_uvar "clear.witness" env' (goal_type goal)
                        (Some (should_check_goal_uvar goal))
                        (goal_typedness_deps goal)
                        (rangeof goal) in
        set_solution goal ut ;!
        replace_cur (mk_goal env' uvar_ut goal.opts goal.is_guard goal.label)
      )

let clear_top () : tac unit =
    let! goal = cur_goal in
    match Env.pop_bv (goal_env goal) with
    | None -> fail "Cannot clear; empty context"
    | Some (x, _) -> clear (S.mk_binder x) // we ignore the qualifier anyway

let prune (s:string) : tac unit =
    let! g = cur_goal in
    let ctx = goal_env g in
    let ctx' = Env.rem_proof_ns ctx (path_of_text s) in
    let g' = goal_with_env g ctx' in
    replace_cur g'

let addns (s:string) : tac unit =
    let! g = cur_goal in
    let ctx = goal_env g in
    let ctx' = Env.add_proof_ns ctx (path_of_text s) in
    let g' = goal_with_env g ctx' in
    replace_cur g'

let guard_formula (g:guard_t) : term =
  match g.guard_f with
  | Trivial -> U.t_true
  | NonTrivial f -> f

let _t_trefl (allow_guards:bool) (l : term) (r : term) : tac unit =
    let should_register_trefl g =
      let should_register = true in
      let skip_register = false in
      if not (Options.compat_pre_core_should_register()) then skip_register else
      //Sending a goal t1 == t2 to the core for registration can be expensive
      //particularly if the terms are big, e.g., when they are WPs etc
      //This function decides which goals to register, using two criteria
      //1. If the uvars in the goal are Allow_untyped or Already_checked
      //   then don't bother registering, since we will not recheck the solution.
      //
      //2. If the goal is of the form `eq2 #ty ?u t` (or vice versa)
      //   and we can prove that ty <: ?u.t
      //   then the assignment of `?u := t` is going to be well-typed
      //   without needing to recompute the type of `t`
      let is_uvar_untyped_or_already_checked u =
        let dec = UF.find_decoration u.ctx_uvar_head in
        match dec.uvar_decoration_should_check with
        | Allow_untyped _
        | Already_checked -> true
        | _ -> false
      in
      let is_uvar t =
        let head = U.leftmost_head t in
        match (SS.compress head).n with
        | Tm_uvar (u, _) -> Inl (u, head, t)
        | _ -> Inr t
      in
      let is_allow_untyped_uvar t =
        match is_uvar t with
        | Inr _ -> false
        | Inl (u, _, _) -> is_uvar_untyped_or_already_checked u
      in
      let t = U.ctx_uvar_typ g.goal_ctx_uvar in
      let uvars = elems (FStarC.Syntax.Free.uvars t) in
      if BU.for_all is_uvar_untyped_or_already_checked uvars
      then skip_register //all the uvars are already checked or untyped
      else (
        let head, args =
          let t =
            match U.un_squash t with
            | None -> t
            | Some t -> t
          in
          U.leftmost_head_and_args t
        in
        match (SS.compress (U.un_uinst head)).n, args with
        | Tm_fvar fv, [(ty, _); (t1, _); (t2, _)]
          when S.fv_eq_lid fv PC.eq2_lid ->
          if is_allow_untyped_uvar t1 || is_allow_untyped_uvar t2
          then skip_register //if we have ?u=t or t=?u and ?u is allow_untyped, then skip
          else if Tactics.Monad.is_goal_safe_as_well_typed g //o.w., if the goal is well typed
          then (
          //and the goal is of the shape
          //   eq2 #ty ?u t or
          //   eq2 #ty t ?u
          // Then solving this, if it succeeds, is going to assign ?u := t
          // If we know that `ty <: ?u.ty` then this is well-typed already
          // without needing to recheck the assignment
          // Note, from well-typedness of the goal, we already know ?u.ty <: ty
          let check_uvar_subtype u t =
            let env = { goal_env g with gamma = g.goal_ctx_uvar.ctx_uvar_gamma } in
            match Core.compute_term_type_handle_guards env t (fun _ _ -> true)
            with
            | Inr _ -> false
            | Inl (_, t_ty) -> (  // ignoring the effect, ghost is ok
              match Core.check_term_subtyping true true env ty t_ty with
              | Inl None -> //unconditional subtype
                mark_uvar_as_already_checked u;
                true
              | _ ->
                false
              )
          in
          match is_uvar t1, is_uvar t2 with
          | Inl (u, _, tu), Inr _
          | Inr _, Inl (u, _, tu) ->
            //if the condition fails, then return true to register this goal
            //since the assignment will have to be rechecked
            if check_uvar_subtype u tu
            then skip_register
            else should_register
          | _ ->
            should_register
          )
          else should_register
        | _ ->
          should_register
      )
  in
  let! g = cur_goal in
  let should_check = should_check_goal_uvar g in
  if should_register_trefl g
  then Tactics.Monad.register_goal g;
  let must_tot = true in
  let attempt (l : term) (r : term) : tac bool =
    match! do_unify_maybe_guards allow_guards must_tot (goal_env g) l r with
    | None -> ret false
    | Some guard ->
      solve' g U.exp_unit ;!
      if allow_guards
      then
        let! goal = goal_of_guard "t_trefl" (goal_env g) (guard_formula guard) (Some should_check) (rangeof g) in
        push_goals [goal] ;!
        ret true
      else
        // If allow_guards is false, this guard must be trivial and we don't
        // add it, but we check its triviality for sanity.
        if Env.is_trivial_guard_formula guard
        then ret true
        else failwith "internal error: _t_refl: guard is not trivial"
  in
  match! attempt l r with
  | true -> ret ()
  | false ->
    (* if that didn't work, normalize and retry *)
    let norm = N.normalize [Env.UnfoldUntil delta_constant; Env.Primops; Env.DontUnfoldAttr [PC.tac_opaque_attr]] (goal_env g) in
    match! attempt (norm l) (norm r) with
    | true -> ret ()
    | false ->
      let ls, rs = TypeChecker.Err.print_discrepancy (tts (goal_env g)) l r in
      fail2 "cannot unify (%s) and (%s)" ls rs

let t_trefl (allow_guards:bool) : tac unit = wrap_err "t_trefl" <| (
  match!
    catch (//restore UF graph, including any Already_checked markers, if anything fails
      let! g = cur_goal in
      match destruct_eq (goal_env g) (goal_type g) with
      | Some (l, r) ->
             _t_trefl allow_guards l r
      | None ->
             fail1 "not an equality (%s)" (tts (goal_env g) (goal_type g))
    )
  with
  | Inr v -> ret v
  | Inl exn -> traise exn
  )

let dup () : tac unit =
  let! g = cur_goal in
  let goal_sc = should_check_goal_uvar g in
  let env = goal_env g in
  let! u, u_uvar =
       new_uvar "dup" env (goal_type g)
                (Some (should_check_goal_uvar g))
                (goal_typedness_deps g)
                (rangeof g) in
  //the new uvar is just as Strict as the original one. So, its assignement will be checked
  //and we have a goal that requires us to prove it equal to the original uvar
  //so we can clear the should_check status of the current uvar
  mark_uvar_as_already_checked g.goal_ctx_uvar;
  let g' = { g with goal_ctx_uvar = u_uvar } in
  dismiss ;!
  let t_eq = U.mk_eq2 (env.universe_of env (goal_type g)) (goal_type g) u (goal_witness g) in
  add_irrelevant_goal g "dup equation" env t_eq (Some goal_sc) ;!
  add_goals [g']

// longest_prefix f l1 l2 = (p, r1, r2) ==> l1 = p@r1 /\ l2 = p@r2
let longest_prefix (f : 'a -> 'a -> bool) (l1 : list 'a) (l2 : list 'a) : list 'a & list 'a & list 'a =
    let rec aux acc l1 l2 =
        match l1, l2 with
        | x::xs, y::ys ->
            if f x y
            then aux (x::acc) xs ys
            else acc, x::xs, y::ys
        | _ ->
            acc, l1, l2
    in
    let pr, t1, t2 = aux [] l1 l2 in
    List.rev pr, t1, t2

// NOTE: duplicated from V2.Basic. Should remove this whole module eventually.
let eq_binding b1 b2 =
    match b1, b2 with
    | S.Binding_var bv1, Binding_var bv2 -> bv_eq bv1 bv2 && U.term_eq bv1.sort bv2.sort
    | S.Binding_lid (lid1, _), Binding_lid (lid2, _) -> lid_equals lid1 lid2
    | S.Binding_univ u1, Binding_univ u2 -> ident_equals u1 u2
    | _ -> false

// fix universes
let join_goals g1 g2 : tac goal =
    (* The one in Syntax.Util ignores null_binders, why? *)
    let close_forall_no_univs bs f =
        List.fold_right (fun b f -> U.mk_forall_no_univ b.binder_bv f) bs f
    in
    match get_phi g1 with
    | None -> fail "goal 1 is not irrelevant"
    | Some phi1 ->
    match get_phi g2 with
    | None -> fail "goal 2 is not irrelevant"
    | Some phi2 ->

    let gamma1 = g1.goal_ctx_uvar.ctx_uvar_gamma in
    let gamma2 = g2.goal_ctx_uvar.ctx_uvar_gamma in
    let gamma, r1, r2 = longest_prefix eq_binding (List.rev gamma1) (List.rev gamma2) in

    let t1 = close_forall_no_univs (Env.binders_of_bindings (List.rev r1)) phi1 in
    let t2 = close_forall_no_univs (Env.binders_of_bindings (List.rev r2)) phi2 in

    let goal_sc =
      match should_check_goal_uvar g1, should_check_goal_uvar g2 with
      | Allow_untyped reason1, Allow_untyped _ -> Some (Allow_untyped reason1)
      | _ -> None
    in
    set_solution g1 U.exp_unit ;!
    set_solution g2 U.exp_unit ;!

    let ng = U.mk_conj t1 t2 in
    let nenv = { goal_env g1 with gamma = List.rev gamma } in
    let! goal = mk_irrelevant_goal "joined" nenv ng goal_sc (rangeof g1) g1.opts g1.label in
    if_verbose (fun () -> BU.print3 "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                         (goal_to_string_verbose g1)
                         (goal_to_string_verbose g2)
                         (goal_to_string_verbose goal)) ;!
    ret goal

let join () : tac unit =
    let! ps = get in
    match ps.goals with
    | g1::g2::gs ->
      set { ps with goals = gs } ;!
      let! g12 = join_goals g1 g2 in
      add_goals [g12]

    | _ -> fail "join: less than 2 goals"


let set_options (s : string) : tac unit = wrap_err "set_options" <| (
    let! g = cur_goal in
    FStarC.Options.push ();
    FStarC.Options.set g.opts;
    let res = FStarC.Options.set_options s in
    let opts' = FStarC.Options.peek () in
    FStarC.Options.pop ();
    match res with
    | FStarC.Getopt.Success ->
        let g' = { g with opts = opts' } in
        replace_cur g'
    | FStarC.Getopt.Error (err, _) ->
        fail2 "Setting options `%s` failed: %s" s err
    | FStarC.Getopt.Help ->
        fail1 "Setting options `%s` failed (got `Help`?)" s
    )

let top_env     () : tac env  = bind get (fun ps -> ret <| ps.main_context)

let lax_on () : tac bool =
    let! g = cur_goal in
    ret (Options.lax () || (goal_env g).admit)

let unquote (ty : term) (tm : term) : tac term = wrap_err "unquote" <| (
    if_verbose (fun () -> BU.print1 "unquote: tm = %s\n" (show tm)) ;!
    let! goal = cur_goal in
    let env = Env.set_expected_typ (goal_env goal) ty in
    let! tm, typ, guard = __tc_ghost env tm in
    if_verbose (fun () -> BU.print1 "unquote: tm' = %s\n" (show tm)) ;!
    if_verbose (fun () -> BU.print1 "unquote: typ = %s\n" (show typ)) ;!
    proc_guard "unquote" env guard (Some (should_check_goal_uvar goal)) (rangeof goal) ;!
    ret tm
    )

let uvar_env (env : env) (ty : option typ) : tac term =
  let! ps = get in
  // If no type was given, add a uvar for it too!
  let! typ, g, r =
    match ty with
    | Some ty ->
      let env = Env.set_expected_typ env (U.type_u () |> fst) in
      let! ty, _, g = __tc_ghost env ty in
      ret (ty, g, ty.pos)

    | None ->
      //the type of this uvar is just Type; so it's typedness deps is []
      let! typ, uvar_typ = new_uvar "uvar_env.2" env (fst <| U.type_u ()) None [] ps.entry_range in
      ret (typ, Env.trivial_guard, Range.dummyRange)
  in
  proc_guard "uvar_env_typ" env g None r;!
  //the guard is an explicit goal; so the typedness deps of this new uvar is []
  let! t, uvar_t = new_uvar "uvar_env" env typ None [] ps.entry_range in
  ret t

let ghost_uvar_env (env : env) (ty : typ) : tac term =
  let! ps = get in
  // If no type was given, add a uvar for it too!
  let! typ, _, g = __tc_ghost env ty in
  proc_guard "ghost_uvar_env_typ" env g None ty.pos ;!
  //the guard is an explicit goal; so the typedness deps of this new uvar is []
  let! t, uvar_t = new_uvar "uvar_env" env typ (Some (Allow_ghost "User ghost uvar")) [] ps.entry_range in
  ret t

let fresh_universe_uvar () : tac term =
  U.type_u () |> fst |> ret

let unshelve (t : term) : tac unit = wrap_err "unshelve" <| (
    let! ps = get in
    let env = ps.main_context in
    (* We need a set of options, but there might be no goals, so do this *)
    let opts = match ps.goals with
               | g::_ -> g.opts
               | _ -> FStarC.Options.peek ()
    in
    match U.head_and_args t with
    | { n = Tm_uvar (ctx_uvar, _) }, _ ->
        let env = {env with gamma=ctx_uvar.ctx_uvar_gamma} in
        let g = mk_goal env ctx_uvar opts false "" in
        let g = bnorm_goal g in
        add_goals [g]
    | _ -> fail "not a uvar"
    )

let tac_and (t1 : tac bool) (t2 : tac bool) : tac bool =
  match! t1 with
  | false -> return false
  | true -> t2

let default_if_err (def : 'a) (t : tac 'a) : tac 'a =
  let! r = catch t in
  match r with
  | Inl _ -> return def
  | Inr v -> return v

let match_env (e:env) (t1 : term) (t2 : term) : tac bool = wrap_err "match_env" <| (
    let! ps = get in
    let! t1, ty1, g1 = __tc e t1 in
    let! t2, ty2, g2 = __tc e t2 in
    proc_guard "match_env g1" e g1 None ps.entry_range ;!
    proc_guard "match_env g2" e g2 None ps.entry_range ;!
    let must_tot = true in
    default_if_err false <|
      tac_and (do_match must_tot e ty1 ty2)
              (do_match must_tot e t1 t2)
    )

let unify_env (e:env) (t1 : term) (t2 : term) : tac bool = wrap_err "unify_env" <| (
    let! ps = get in
    let! t1, ty1, g1 = __tc e t1 in
    let! t2, ty2, g2 = __tc e t2 in
    proc_guard "unify_env g1" e g1 None ps.entry_range ;!
    proc_guard "unify_env g2" e g2 None ps.entry_range ;!
    let must_tot = true in
    default_if_err false <|
      tac_and (do_unify must_tot e ty1 ty2)
              (do_unify must_tot e t1 t2)
    )

let unify_guard_env (e:env) (t1 : term) (t2 : term) : tac bool = wrap_err "unify_guard_env" <| (
    let! ps = get in
    let! t1, ty1, g1 = __tc e t1 in
    let! t2, ty2, g2 = __tc e t2 in
    proc_guard "unify_guard_env g1" e g1 None ps.entry_range ;!
    proc_guard "unify_guard_env g2" e g2 None ps.entry_range ;!
    let must_tot = true in
    match! do_unify_maybe_guards true must_tot e ty1 ty2 with
    | None -> ret false
    | Some g1 ->
      match! do_unify_maybe_guards true must_tot e t1 t2 with
      | None -> ret false
      | Some g2 ->
        let formula : term = U.mk_conj (guard_formula g1) (guard_formula g2) in
        let! goal = goal_of_guard "unify_guard_env.g2" e formula None ps.entry_range in
        push_goals [goal] ;!
        ret true
    )

let launch_process (prog : string) (args : list string) (input : string) : tac string =
    // The `bind idtac` thunks the tactic
    idtac ;!
    if Options.unsafe_tactic_exec () then
        let s = BU.run_process "tactic_launch" prog args (Some input) in
        ret s
    else
        fail "launch_process: will not run anything unless --unsafe_tactic_exec is provided"

let fresh_bv_named (nm : string) : tac bv =
    // The `bind idtac` thunks the tactic. Not really needed, just being paranoid
    idtac ;! ret (gen_bv nm None S.tun)

let change (ty : typ) : tac unit = wrap_err "change" <| (
    if_verbose (fun () -> BU.print1 "change: ty = %s\n" (show ty)) ;!
    let! g = cur_goal in
    let! ty, _, guard = __tc (goal_env g) ty in
    proc_guard "change" (goal_env g) guard (Some (should_check_goal_uvar g)) (rangeof g) ;!
    let must_tot = true in
    let! bb = do_unify must_tot (goal_env g) (goal_type g) ty in
    if bb
    then replace_cur (goal_with_type g ty)
    else begin
        (* Give it a second try, fully normalize the term the user gave
         * and unify it with the fully normalized goal. If that succeeds,
         * we use the original one as the new goal. This is sometimes needed
         * since the unifier has some bugs. *)
        let steps = [Env.AllowUnboundUniverses; Env.UnfoldUntil delta_constant; Env.Primops] in
        let ng  = normalize steps (goal_env g) (goal_type g) in
        let nty = normalize steps (goal_env g) ty in
        let! b = do_unify must_tot (goal_env g) ng nty in
        if b
        then replace_cur (goal_with_type g ty)
        else fail "not convertible"
    end
    )

let failwhen (b:bool) (msg:string) : tac unit =
    if b
    then fail msg
    else ret ()

let t_destruct (s_tm : term) : tac (list (fv & Z.t)) = wrap_err "destruct" <| (
    let! g = cur_goal in
    let! s_tm, s_ty, guard = __tc (goal_env g) s_tm in
    proc_guard "destruct" (goal_env g) guard (Some (should_check_goal_uvar g)) (rangeof g) ;!
    let s_ty = N.normalize [Env.DontUnfoldAttr [PC.tac_opaque_attr]; Env.Weak; Env.HNF; Env.UnfoldUntil delta_constant]
                           (goal_env g) s_ty in
    let h, args = U.head_and_args_full (U.unrefine s_ty) in
    let! fv, a_us =
         match (SS.compress h).n with
         | Tm_fvar fv -> ret (fv, [])
         | Tm_uinst (h', us) ->
           begin match (SS.compress h').n with
           | Tm_fvar fv -> ret (fv, us)
           | _ -> failwith "impossible: uinst over something that's not an fvar"
           end
         | _ -> fail "type is not an fv"
    in
    let t_lid = lid_of_fv fv in
    match Env.lookup_sigelt (goal_env g) t_lid with
    | None -> fail "type not found in environment"
    | Some se ->
      match se.sigel with
      | Sig_inductive_typ {us=t_us; params=t_ps; t=t_ty; mutuals=mut; ds=c_lids} ->
      (* High-level idea of this huge function:
       * For  Gamma |- w : phi  and  | C : ps -> bs -> t,  we generate a new goal
       *   Gamma |- w' : bs -> phi
       * with
       *   w = match tm with ... | C .ps' bs' -> w' bs' ...
       * i.e., we do not intro the matched binders and let the
       * user do that (with the returned arity). `.ps` represents inaccesible patterns
       * for the type's parameters.
       *)
      let erasable = U.has_attribute se.sigattrs FStarC.Parser.Const.erasable_attr in
      failwhen (erasable && not (is_irrelevant g)) "cannot destruct erasable type to solve proof-relevant goal" ;!

      (* Instantiate formal universes to the actuals,
       * and substitute accordingly in binders and types *)
      failwhen (List.length a_us <> List.length t_us) "t_us don't match?" ;!


      (* Not needed currently? *)
      (* let s = Env.mk_univ_subst t_us a_us in *)
      (* let t_ps = SS.subst_binders s t_ps in *)
      (* let t_ty = SS.subst         s t_ty in *)
      let t_ps, t_ty = SS.open_term t_ps t_ty in

      let! goal_brs =
           mapM (fun c_lid ->
                    match Env.lookup_sigelt (goal_env g) c_lid with
                    | None -> fail "ctor not found?"
                    | Some se ->
                    match se.sigel with
                    | Sig_datacon {us=c_us; t=c_ty; num_ty_params=nparam; mutuals=mut} ->
                        (* BU.print2 "ty of %s = %s\n" (show c_lid) *)
                        (*                             (show c_ty); *)
                        let fv = S.lid_as_fv c_lid (Some Data_ctor) in


                        failwhen (List.length a_us <> List.length c_us) "t_us don't match?" ;!
                        let s = Env.mk_univ_subst c_us a_us in
                        let c_ty = SS.subst s c_ty in

                        (* The constructor might be universe-polymorphic, just use
                         * fresh univ_uvars for its universes. *)
                        let c_us, c_ty = Env.inst_tscheme (c_us, c_ty) in

                        (* BU.print2 "ty(2) of %s = %s\n" (show c_lid) *)
                        (*                                (show c_ty); *)

                        (* Deconstruct its type, separating the parameters from the
                         * actual arguments (indices do not matter here). *)
                        let bs, comp = U.arrow_formals_comp c_ty in

                        (* More friendly names: 'a_i' instead of '_i' *)
                        let bs, comp =
                          let rename_bv bv =
                              let ppname = bv.ppname in
                              let ppname = mk_ident ("a" ^ show ppname, range_of_id ppname) in
                              // freshen just to be extra safe.. probably not needed
                              freshen_bv ({ bv with ppname = ppname })
                          in
                          let bs' = List.map (fun b -> {b with binder_bv=rename_bv b.binder_bv}) bs in
                          let subst = List.map2 (fun ({binder_bv=bv}) ({binder_bv=bv'}) -> NT (bv, bv_to_name bv')) bs bs' in
                          SS.subst_binders subst bs', SS.subst_comp subst comp
                        in

                        (* BU.print1 "bs = (%s)\n" (Print.binders_to_string ", " bs); *)
                        let d_ps, bs = List.splitAt nparam bs in
                        failwhen (not (U.is_total_comp comp)) "not total?" ;!
                        let mk_pat p = { v = p; p = s_tm.pos } in
                        (* TODO: This is silly, why don't we just keep aq in the Pat_cons? *)
                        let is_imp = function | Some (Implicit _) -> true
                                              | _ -> false
                        in
                        let a_ps, a_is = List.splitAt nparam args in
                        failwhen (List.length a_ps <> List.length d_ps) "params not match?" ;!
                        let d_ps_a_ps = List.zip d_ps a_ps in
                        let subst = List.map (fun (({binder_bv=bv}), (t, _)) -> NT (bv, t)) d_ps_a_ps in
                        let bs = SS.subst_binders subst bs in
                        let subpats_1 = List.map (fun (({binder_bv=bv}), (t, _)) ->
                                                 (mk_pat (Pat_dot_term (Some t)), true)) d_ps_a_ps in
                        let subpats_2 = List.map (fun ({binder_bv=bv;binder_qual=bq}) ->
                                                 (mk_pat (Pat_var bv), is_imp bq)) bs in
                        let subpats = subpats_1 @ subpats_2 in
                        let pat = mk_pat (Pat_cons (fv, Some a_us, subpats)) in
                        let env = (goal_env g) in


                        (* Add an argument stating the equality between the scrutinee
                         * and the pattern, in-scope for this branch. *)
                        let cod = goal_type g in
                        let equ = env.universe_of env s_ty in
                        (* Typecheck the pattern, to fill-in the universes and get an expression out of it *)
                        let _ , _, _, _, pat_t, _, _guard_pat, _erasable = TcTerm.tc_pat ({ env with admit = true }) s_ty pat in
                        let eq_b = S.gen_bv "breq" None (U.mk_squash S.U_zero (U.mk_eq2 equ s_ty s_tm pat_t)) in
                        let cod = U.arrow [S.mk_binder eq_b] (mk_Total cod) in

                        let nty = U.arrow bs (mk_Total cod) in
                        let! uvt, uv = new_uvar "destruct branch" env nty None (goal_typedness_deps g) (rangeof g) in
                        let g' = mk_goal env uv g.opts false g.label in
                        let brt = U.mk_app_binders uvt bs in
                        (* Provide the scrutinee equality, which is trivially provable *)
                        let brt = U.mk_app brt [S.as_arg U.exp_unit] in
                        let br = SS.close_branch (pat, None, brt) in
                        ret (g', br, (fv, Z.of_int_fs (List.length bs)))
                    | _ ->
                        fail "impossible: not a ctor")
                 c_lids
      in
      let goals, brs, infos = List.unzip3 goal_brs in
      let w = mk (Tm_match {scrutinee=s_tm;ret_opt=None;brs;rc_opt=None}) s_tm.pos in
      solve' g w ;!
      //we constructed a well-typed term to solve g; no need to recheck it
      mark_goal_implicit_already_checked g;
      add_goals goals ;!
      ret infos

    | _ -> fail "not an inductive type"
    )

let gather_explicit_guards_for_resolved_goals ()
  : tac unit
  = ret ()

// TODO: move to library?
let rec last (l:list 'a) : 'a =
    match l with
    | [] -> failwith "last: empty list"
    | [x] -> x
    | _::xs -> last xs

let rec init (l:list 'a) : list 'a =
    match l with
    | [] -> failwith "init: empty list"
    | [x] -> []
    | x::xs -> x :: init xs

(* TODO: to avoid the duplication with inspect_ln (and the same
for pack), we could instead have an `open_view` function (maybe even
user-facing?) that takes care of opening the needed binders in the rest
of the term. Similarly, a `close_view`. Then:

  inspect = open_view . inspect_ln
  pack    = pack_ln . close_view

which would be nice. But.. patterns in matches and recursive
letbindings make that complicated, since we need to duplicate a bunch of
logic from Syntax.Subst here, so I dropped that idea for now.
Everything else goes surprisingly smooth though!

-- GM 2022/Oct/05
*)

let rec inspect (t:term) : tac term_view = wrap_err "inspect" (
    let! e = top_env () in
    let t = U.unlazy_emb t in
    let t = SS.compress t in
    match t.n with
    | Tm_meta {tm=t} ->
        inspect t

    | Tm_name bv ->
        ret <| Tv_Var bv

    | Tm_bvar bv ->
        ret <| Tv_BVar bv

    | Tm_fvar fv ->
        ret <| Tv_FVar fv

    | Tm_uinst (t, us) ->
      (match (t |> SS.compress |> U.unascribe).n with
       | Tm_fvar fv -> ret <| Tv_UInst (fv, us)
       | _ -> failwith "Tac::inspect: Tm_uinst head not an fvar")

    | Tm_ascribed {tm=t; asc=(Inl ty, tacopt, eq)} ->
        ret <| Tv_AscribedT (t, ty, tacopt, eq)

    | Tm_ascribed {tm=t; asc=(Inr cty, tacopt, eq)} ->
        ret <| Tv_AscribedC (t, cty, tacopt, eq)

    | Tm_app {args=[]} ->
        failwith "empty arguments on Tm_app"

    | Tm_app {hd; args} ->
        // We split at the last argument, since the term_view does not
        // expose n-ary lambdas buy unary ones.
        let (a, q) = last args in
        let q' = inspect_aqual q in
        ret <| Tv_App (S.mk_Tm_app hd (init args) t.pos, (a, q')) // TODO: The range and tk are probably wrong. Fix

    | Tm_abs {bs=[]} ->
        failwith "empty arguments on Tm_abs"

    | Tm_abs {bs; body=t; rc_opt=k} ->
        let bs, t = SS.open_term bs t in
        // `let b::bs = bs` gives a coverage warning, avoid it
        begin match bs with
        | [] -> failwith "impossible"
        | b::bs -> ret <| Tv_Abs (b, U.abs bs t k)
        end

    | Tm_type u ->
        ret <| Tv_Type u

    | Tm_arrow {bs=[]} ->
        failwith "empty binders on arrow"

    | Tm_arrow _ ->
        begin match U.arrow_one t with
        | Some (b, c) -> ret <| Tv_Arrow (b, c)
        | None -> failwith "impossible"
        end

    | Tm_refine {b=bv; phi=t} ->
        let b = S.mk_binder bv in
        let b', t = SS.open_term [b] t in
        // `let [b] = b'` gives a coverage warning, avoid it
        let b = (match b' with
        | [b'] -> b'
        | _ -> failwith "impossible") in
        ret <| Tv_Refine (b.binder_bv, b.binder_bv.sort, t)

    | Tm_constant c ->
        ret <| Tv_Const (inspect_const c)

    | Tm_uvar (ctx_u, s) ->
        ret <| Tv_Uvar (Z.of_int_fs (UF.uvar_unique_id ctx_u.ctx_uvar_head), (ctx_u, s))

    | Tm_let {lbs=(false, [lb]); body=t2} ->
        if lb.lbunivs <> [] then ret <| Tv_Unsupp else
        begin match lb.lbname with
        | Inr _ -> ret <| Tv_Unsupp // no top level lets
        | Inl bv ->
            // The type of `bv` should match `lb.lbtyp`
            let b = S.mk_binder bv in
            let bs, t2 = SS.open_term [b] t2 in
            let b = match bs with
                    | [b] -> b
                    | _ -> failwith "impossible: open_term returned different amount of binders"
            in
            ret <| Tv_Let (false, lb.lbattrs, b.binder_bv, bv.sort, lb.lbdef, t2)
        end

    | Tm_let {lbs=(true, [lb]); body=t2} ->
        if lb.lbunivs <> [] then ret <| Tv_Unsupp else
        begin match lb.lbname with
        | Inr _ -> ret <| Tv_Unsupp // no top level lets
        | Inl bv ->
            let lbs, t2 = SS.open_let_rec [lb] t2 in
            match lbs with
            | [lb] ->
                (match lb.lbname with
                 | Inr _ -> ret Tv_Unsupp
                 | Inl bv -> ret <| Tv_Let (true, lb.lbattrs, bv, bv.sort, lb.lbdef, t2))
            | _ -> failwith "impossible: open_term returned different amount of binders"
        end

    | Tm_match {scrutinee=t; ret_opt; brs} ->
        let rec inspect_pat p =
            match p.v with
            | Pat_constant c -> Pat_Constant (inspect_const c)
            | Pat_cons (fv, us_opt, ps) -> Pat_Cons (fv, us_opt, List.map (fun (p, b) -> inspect_pat p, b) ps)
            | Pat_var bv -> Pat_Var (bv, Sealed.seal bv.sort)
            | Pat_dot_term eopt -> Pat_Dot_Term eopt
        in
        let brs = List.map SS.open_branch brs in
        let brs = List.map (function (pat, _, t) -> (inspect_pat pat, t)) brs in
        ret <| Tv_Match (t, ret_opt, brs)

    | Tm_unknown ->
        ret <| Tv_Unknown

    | _ ->
      Err.log_issue t Err.Warning_CantInspect
        (BU.format2 "inspect: outside of expected syntax (%s, %s)\n" (tag_of t) (show t));
      ret <| Tv_Unsupp
    )

(* This function could actually be pure, it doesn't need freshness
 * like `inspect` does, but we mark it as Tac for uniformity. *)
let pack' (tv:term_view) (leave_curried:bool) : tac term =
    match tv with
    | Tv_Var bv ->
        ret <| S.bv_to_name bv

    | Tv_BVar bv ->
        ret <| S.bv_to_tm bv

    | Tv_FVar fv ->
        ret <| S.fv_to_tm fv

    | Tv_UInst (fv, us) ->
        ret <| S.mk_Tm_uinst (S.fv_to_tm fv) us

    | Tv_App (l, (r, q)) ->
        let q' = pack_aqual q in
        ret <| U.mk_app l [(r, q')]

    | Tv_Abs (b, t) ->
        ret <| U.abs [b] t None // TODO: effect?

    | Tv_Arrow (b, c) ->
        ret <| (if leave_curried then U.arrow [b] c else U.canon_arrow (U.arrow [b] c))

    | Tv_Type u ->
        ret <| S.mk (Tm_type u) Range.dummyRange

    | Tv_Refine (bv, sort, t) ->
        let bv = { bv with sort = sort } in
        ret <| U.refine bv t

    | Tv_Const c ->
        ret <| S.mk (Tm_constant (pack_const c)) Range.dummyRange

    | Tv_Uvar (_u, ctx_u_s) ->
        ret <| S.mk (Tm_uvar ctx_u_s) Range.dummyRange

    | Tv_Let (false, attrs, bv, ty, t1, t2) ->
        let bv = { bv with sort = ty } in
        let lb = U.mk_letbinding (Inl bv) [] bv.sort PC.effect_Tot_lid t1 attrs Range.dummyRange in
        ret <| S.mk (Tm_let {lbs=(false, [lb]); body=SS.close [S.mk_binder bv] t2}) Range.dummyRange

    | Tv_Let (true, attrs, bv, ty, t1, t2) ->
        let bv = { bv with sort = ty } in
        let lb = U.mk_letbinding (Inl bv) [] bv.sort PC.effect_Tot_lid t1 attrs Range.dummyRange in
        let lbs, body = SS.close_let_rec [lb] t2 in
        ret <| S.mk (Tm_let {lbs=(true, lbs); body}) Range.dummyRange

    | Tv_Match (t, ret_opt, brs) ->
        let wrap v = {v=v;p=Range.dummyRange} in
        let rec pack_pat p : S.pat =
            match p with
            | Pat_Constant c -> wrap <| Pat_constant (pack_const c)
            | Pat_Cons (fv, us_opt, ps) -> wrap <| Pat_cons (fv, us_opt, List.map (fun (p, b) -> pack_pat p, b) ps)
            | Pat_Var  (bv, _sort) -> wrap <| Pat_var bv
            | Pat_Dot_Term eopt -> wrap <| Pat_dot_term eopt
        in
        let brs = List.map (function (pat, t) -> (pack_pat pat, None, t)) brs in
        let brs = List.map SS.close_branch brs in
        ret <| S.mk (Tm_match {scrutinee=t; ret_opt; brs; rc_opt=None}) Range.dummyRange

    | Tv_AscribedT(e, t, tacopt, use_eq) ->
        ret <| S.mk (Tm_ascribed {tm=e;asc=(Inl t, tacopt, use_eq);eff_opt=None}) Range.dummyRange

    | Tv_AscribedC(e, c, tacopt, use_eq) ->
        ret <| S.mk (Tm_ascribed {tm=e;asc=(Inr c, tacopt, use_eq);eff_opt=None}) Range.dummyRange

    | Tv_Unknown ->
        ret <| S.mk Tm_unknown Range.dummyRange

    | Tv_Unsupp ->
        fail "cannot pack Tv_Unsupp"

let pack (tv:term_view) : tac term = pack' tv false
let pack_curried (tv:term_view) : tac term = pack' tv true

let lget (ty:term) (k:string) : tac term = wrap_err "lget" <| (
    let! ps = get in
    match PSMap.try_find ps.local_state k with
    | None -> fail "not found"
    | Some t -> unquote ty t
    )

let lset (_ty:term) (k:string) (t:term) : tac unit = wrap_err "lset" <| (
    let! ps = get in
    let ps = { ps with local_state = PSMap.add ps.local_state k t } in
    set ps
    )

let set_urgency (u:Z.t) : tac unit =
    let! ps = get in
    let ps = { ps with urgency = Z.to_int_fs u } in
    set ps

let t_commute_applied_match () : tac unit = wrap_err "t_commute_applied_match" <| (
  let! g = cur_goal in
  match destruct_eq (goal_env g) (goal_type g) with
  | Some (l, r) -> begin
    let lh, las = U.head_and_args_full l in
    match (SS.compress (U.unascribe lh)).n with
    | Tm_match {scrutinee=e;ret_opt=asc_opt;brs;rc_opt=lopt} ->
      let brs' = List.map (fun (p, w, e) -> p, w, U.mk_app e las) brs in
      //
      // If residual comp is set, apply arguments to it
      //
      let lopt' = lopt |> BU.map_option (fun rc -> {rc with residual_typ=
        rc.residual_typ |> BU.map_option (fun t ->
          let bs, c = N.get_n_binders (goal_env g) (List.length las) t in
          let bs, c = SS.open_comp bs c in
          let ss = List.map2 (fun b a -> NT (b.binder_bv, fst a)) bs las in
          let c = SS.subst_comp ss c in
          U.comp_result c)}) in
      let l' = mk (Tm_match {scrutinee=e;ret_opt=asc_opt;brs=brs';rc_opt=lopt'}) l.pos in
      let must_tot = true in
      begin match! do_unify_maybe_guards false must_tot (goal_env g) l' r with
      | None -> fail "discharging the equality failed"
      | Some guard ->
        if Env.is_trivial_guard_formula guard
        then (
          //we just checked that its guard is trivial; so no need to check again
          mark_uvar_as_already_checked g.goal_ctx_uvar;
          solve g U.exp_unit
        )
        else failwith "internal error: _t_refl: guard is not trivial"
      end
    | _ ->
      fail "lhs is not a match"
    end
  | None ->
    fail "not an equality"
  )

let string_to_term (e: Env.env) (s: string): tac term
  = let open FStarC.Parser.ParseIt in
    let frag_of_text s = { frag_fname= "<string_to_term>"
                         ; frag_line = 1 ; frag_col  = 0
                         ; frag_text = s } in
    match parse None (Fragment (frag_of_text s)) with
    | Term t ->
      let dsenv = FStarC.Syntax.DsEnv.set_current_module e.dsenv (current_module e) in
      begin try ret (FStarC.ToSyntax.ToSyntax.desugar_term dsenv t) with
          | FStarC.Errors.Error (_, e, _, _) -> fail ("string_to_term: " ^ Errors.rendermsg e)
          | _ -> fail ("string_to_term: Unknown error")
      end
    | ASTFragment _ -> fail ("string_to_term: expected a Term as a result, got an ASTFragment")
    | ParseError (_, err, _) -> fail ("string_to_term: got error " ^ Errors.rendermsg err) // FIXME

let push_bv_dsenv (e: Env.env) (i: string): tac (env & bv)
  = let ident = Ident.mk_ident (i, FStarC.Range.dummyRange) in
    let dsenv, bv = FStarC.Syntax.DsEnv.push_bv e.dsenv ident in
    ret ({ e with dsenv }, bv)

let term_to_string (t:term) : tac string
  = let s = show t in
    ret s

let comp_to_string (c:comp) : tac string
  = let s = show c in
    ret s

let range_to_string (r:FStarC.Range.range) : tac string
  = ret (show r)

let term_eq_old (t1:term) (t2:term) : tac bool
  = idtac ;!
    ret (Syntax.Util.term_eq t1 t2)

let with_compat_pre_core (n:Z.t) (f:tac 'a) : tac 'a =
    mk_tac (fun ps ->
      Options.with_saved_options (fun () ->
        let _res = FStarC.Options.set_options ("--compat_pre_core 0") in
        run f ps))

let get_vconfig () : tac vconfig =
  let! g = cur_goal in
 (* Restore goal's optionstate (a copy is needed) and read vconfig.
  * This is an artifact of the options API being stateful in many places,
  * morally this is just (get_vconfig g.opts) *)
  let vcfg = Options.with_saved_options (fun () ->
               FStarC.Options.set g.opts;
               Options.get_vconfig ())
  in
  ret vcfg

let set_vconfig (vcfg : vconfig) : tac unit =
  (* Same comment as for get_vconfig applies, this is really just
   * let g' = { g with opts = set_vconfig vcfg g.opts } *)
  let! g = cur_goal in
  let opts' = Options.with_saved_options (fun () ->
                FStarC.Options.set g.opts;
                Options.set_vconfig vcfg;
                Options.peek ())
  in
  let g' = { g with opts = opts' } in
  replace_cur g'

let t_smt_sync (vcfg : vconfig) : tac unit = wrap_err "t_smt_sync" <| (
    let! goal = cur_goal in
    match get_phi goal with
    | None -> fail "Goal is not irrelevant"
    | Some phi ->
      let e = goal_env goal in
      let ans : bool =
        (* Set goal's optionstate before asking solver, to respect
         * its vconfig among other things. *)
        Options.with_saved_options (fun () ->
          (* NOTE: we ignore the goal's options, the rationale is that
           * any verification-relevant option is inside the vconfig, so we
           * should not need read the optionstate. Of course this vconfig
           * will probably come in large part from a get_vconfig, which does
           * read the goal's options. *)
          Options.set_vconfig vcfg;
          e.solver.solve_sync None e phi
        )
      in
      if ans
      then (
        mark_uvar_as_already_checked goal.goal_ctx_uvar;
        solve goal U.exp_unit
      ) else fail "SMT did not solve this goal"
)

let free_uvars (tm : term) : tac (list Z.t)
  = idtac ;!
    let uvs = Syntax.Free.uvars_uncached tm |> elems |> List.map (fun u -> Z.of_int_fs (UF.uvar_id u.ctx_uvar_head)) in
    ret uvs

(***** Builtins used in the meta DSL framework *****)

let dbg_refl (g:env) (msg:unit -> string) =
  if !dbg_ReflTc
  then BU.print_string (msg ())

let issues = list Errors.issue
let refl_typing_builtin_wrapper (f:unit -> 'a) : tac (option 'a & issues) =
  let tx = UF.new_transaction () in
  let errs, r = 
    try Errors.catch_errors_and_ignore_rest f
    with exn -> //catch everything
      let issue = FStarC.Errors.({
        issue_msg = Errors.mkmsg (BU.print_exn exn);
        issue_level = EError;
        issue_range = None;
        issue_number = (Some 17);
        issue_ctx = get_ctx ()
      }) in
      [issue], None
  in
  UF.rollback tx;
  if List.length errs > 0
  then ret (None, errs)
  else ret (r, errs)

let no_uvars_in_term (t:term) : bool =
  t |> Free.uvars |> is_empty &&
  t |> Free.univs |> is_empty

let no_uvars_in_g (g:env) : bool =
  g.gamma |> BU.for_all (function
    | Binding_var bv -> no_uvars_in_term bv.sort
    | _ -> true)

type relation =
  | Subtyping
  | Equality

let unexpected_uvars_issue r =
  let open FStarC.Errors in
  let i = {
    issue_level = EError;
    issue_range = Some r;
    issue_msg = Errors.mkmsg "Cannot check relation with uvars";
    issue_number = Some (errno Error_UnexpectedUnresolvedUvar);
    issue_ctx = []
  } in
  i

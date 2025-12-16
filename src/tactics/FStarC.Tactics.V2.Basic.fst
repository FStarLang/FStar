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
module FStarC.Tactics.V2.Basic

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Ident
open FStarC.TypeChecker.Env
open FStarC.TypeChecker.Common
open FStarC.Pprint
open FStarC.Reflection.V2.Data
open FStarC.Reflection.V2.Builtins
open FStarC.Tactics.Common
open FStarC.Tactics.Result
open FStarC.Tactics.Types
open FStarC.Tactics.Monad
open FStarC.Tactics.Printing
open FStarC.Syntax.Syntax
open FStarC.VConfig
open FStarC.Errors.Msg
module Listlike = FStarC.Class.Listlike

module BU     = FStarC.Util
module Cfg    = FStarC.TypeChecker.Cfg
module Env    = FStarC.TypeChecker.Env
module Err    = FStarC.Errors
module N      = FStarC.TypeChecker.Normalize
module PC     = FStarC.Parser.Const
module Print  = FStarC.Syntax.Print
module Free   = FStarC.Syntax.Free
module RD     = FStarC.Reflection.V2.Data
module Rel    = FStarC.TypeChecker.Rel
module SF     = FStarC.Syntax.Free
module S      = FStarC.Syntax.Syntax
module SS     = FStarC.Syntax.Subst
module SC     = FStarC.Syntax.Compress
module TcComm = FStarC.TypeChecker.Common
module TcTerm = FStarC.TypeChecker.TcTerm
module UF     = FStarC.Syntax.Unionfind
module U      = FStarC.Syntax.Util
module Core   = FStarC.TypeChecker.Core
module PO     = FStarC.TypeChecker.Primops
module TC     = FStar.Tactics.Typeclasses

let dbg_Tac        = Debug.get_toggle "Tac"
let dbg_TacUnify   = Debug.get_toggle "TacUnify"
let dbg_2635       = Debug.get_toggle "2635"
let dbg_ReflTc     = Debug.get_toggle "ReflTc"
let dbg_TacVerbose = Debug.get_toggle "TacVerbose"

open FStarC.Class.Show
open FStarC.Class.Monad
open FStarC.Class.PP
open FStarC.Class.Setlike

let fixup_range (r : FStarC.Range.t) : tac (FStarC.Range.t) =
  return (Errors.maybe_bound_range r)

let compress (t:term) : tac term =
  return ();!
  return (SS.compress t)

let compress_univ (u:universe) : tac universe =
  return ();!
  return (SS.compress_univ u)

let core_check env sol t must_tot
  : either (option Core.guard_and_tok_t) Core.error
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
               Format.print5 "(%s) Core checking failed (%s) on term %s and type %s\n%s\n"
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
let ttd = N.term_to_doc

let bnorm_goal g = goal_with_type g (bnorm (goal_env g) (goal_type g))

let tacprint  (s:string)       = Format.print1 "TAC>> %s\n" s
let tacprint1 (s:string) x     = Format.print1 "TAC>> %s\n" (Format.fmt1 s x)
let tacprint2 (s:string) x y   = Format.print1 "TAC>> %s\n" (Format.fmt2 s x y)
let tacprint3 (s:string) x y z = Format.print1 "TAC>> %s\n" (Format.fmt3 s x y z)

let print (msg:string) : tac unit =
    if not (Options.silent ()) || Options.interactive () then
      tacprint msg;
    return ()

let debugging () : tac bool =
    return ();! (* thunk *)
    return !dbg_Tac

let ide () : tac bool =
    return ();! (* thunk *)
    return (Options.ide ())

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
    let uvs = SF.uvars (goal_type g) |> elems in // elems order dependent but OK
    let gs = List.map (goal_of_ctx_uvar g) uvs in
    let gs = List.filter (fun g -> not (check_goal_solved g)) gs in
    let ps' = { ps with smt_goals = [] ; goals = gs } in
    do_dump_ps msg ps';
    Success ((), ps))

let fail1 msg x     = fail (Format.fmt1 msg x)
let fail2 msg x y   = fail (Format.fmt2 msg x y)
let fail3 msg x y z = fail (Format.fmt3 msg x y z)
let fail4 msg x y z w = fail (Format.fmt4 msg x y z w)

let destruct_eq' (typ : typ) : option (term & term) =
    let open FStarC.Syntax.Formula in
    (* destruct_typ_as_formula will do a very conservative unmeta, removing
    Meta_monadic and Meta_monadic_lift nodes, but not Meta_labeled, since that
    leads to bad error messages elsewhere. We don't care about that here, so do
    an aggressive unmeta before calling it. *)
    let typ = U.unmeta typ in
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
        let hd, args = U.head_and_args_full t in
        match (SS.compress hd).n, args with
        | Tm_fvar fv, [(_, Some ({ aqual_implicit = true })); (e1, None); (e2, None)] when S.fv_eq_lid fv PC.op_Eq ->
            Some (e1, e2)
        | _ -> None
        end

let destruct_eq (env : Env.env) (typ : typ) : option (term & term) =
// TODO: unascribe?
    (* let typ = whnf env typ in *)
    match destruct_eq' typ with
    | Some t -> Some t
    | None ->
        // Retry for a squashed one
        begin match U.un_squash typ with
        | Some typ ->
          (* let typ = whnf env typ in *)
          destruct_eq' typ
        | None -> None
        end


let get_guard_policy () : tac guard_policy =
  let! ps = get in
  return ps.guard_policy

let set_guard_policy (pol : guard_policy) : tac unit =
  let! ps = get in
  set ({ ps with guard_policy = pol })

let with_policy pol (t : tac 'a) : tac 'a =
  let! old_pol = get_guard_policy () in
  set_guard_policy pol;!
  let! r = t in
  set_guard_policy old_pol;!
  return r

let proc_guard_formula
  (reason:string) (e : env) (f : term) (tok:option Core.guard_commit_token_cb) (sc_opt : option should_check_uvar)
  (rng:Range.t)
: tac unit
= let! ps = get in
  if !dbg_Tac then
    Format.print2 "Guard policy is %s, trying to discharge %s\n"
      (show ps.guard_policy) (show f);
  let commit_guard_token () =
    match tok with
    | Some tok -> Core.commit_guard tok
    | None -> ()
  in
  match ps.guard_policy with
  | Drop ->
    // should somehow taint the state instead of just printing a warning
    Err.log_issue e Errors.Warning_TacAdmit
      (Format.fmt1 "Tactics admitted guard <%s>\n\n" (show f));
    return ()

  | Goal ->
    log (fun () -> Format.print2 "Making guard (%s:%s) into a goal\n" reason (show f));!
    let! g = goal_of_guard reason e f sc_opt rng in
    push_goals [g]

  | SMT ->
    log (fun () -> Format.print2 "Pushing guard (%s:%s) as SMT goal\n" reason (show f));!
    let! g = goal_of_guard reason e f sc_opt rng in
    push_smt_goals [g]

  | SMTSync ->
    log (fun () -> Format.print2 "Sending guard (%s:%s) to SMT Synchronously\n" reason (show f));!
    let g = { Env.trivial_guard with guard_f = NonTrivial f } in
    Rel.force_trivial_guard e g;
    commit_guard_token ();
    return ()

  | Force ->
    log (fun () -> Format.print2 "Forcing guard (%s:%s)\n" reason (show f));!
    let g = { Env.trivial_guard with guard_f = NonTrivial f } in
    begin try
      if not (Env.is_trivial <| Rel.discharge_guard_no_smt e g)
      then fail1 "Forcing the guard failed (%s)" reason
      else (
        commit_guard_token ();
        return ()
      )
    with
    | e ->
      log (fun () -> Format.print1 "guard = %s\n" (show f));!
      fail2 "Forcing the guard failed (%s)\n%s\n" reason (BU.message_of_exn e)
    end

  | ForceSMT ->
    log (fun () -> Format.print2 "Forcing guard WITH SMT (%s:%s)\n" reason (show f));!
    let g = { Env.trivial_guard with guard_f = NonTrivial f } in
    try if not (Env.is_trivial <| Rel.discharge_guard e g)
        then fail1 "Forcing the guard failed (%s)" reason
        else (
          commit_guard_token ();
          return ()
        )
    with
    | e ->
      log (fun () -> Format.print1 "guard = %s\n" (show f));!
      fail2 "Forcing the guard failed (%s)\n%s\n" reason (BU.message_of_exn e)

let proc_guard' (simplify:bool) (reason:string) (e : env) (g : guard_t) (tok:option Core.guard_commit_token_cb) (sc_opt:option should_check_uvar) (rng:Range.t) : tac unit =
    log (fun () -> Format.print2 "Processing guard (%s:%s)\n" reason (Rel.guard_to_string e g));!
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
    | TcComm.Trivial -> return ()
    | TcComm.NonTrivial f ->
      proc_guard_formula reason e f tok sc_opt rng

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
      return ()
    | Already_checked ->
      return ()
    | _ ->
      match UF.find u.ctx_uvar_head with
      | None ->
        return () //not solved yet
      | Some sol ->  //solved, check it
        let env = {env with gamma=u.ctx_uvar_gamma} in
        let must_tot = must_tot && not (Allow_ghost? dec.uvar_decoration_should_check) in
        match core_check env sol (U.ctx_uvar_typ u) must_tot with
        | Inl None ->
          //checked with no guard
          //no need to check it again
          mark_uvar_as_already_checked u;
          return ()

        | Inl (Some (g, guard_tok)) ->
          let guard = { Env.trivial_guard with guard_f = NonTrivial g } in
          let guard = Rel.simplify_guard env guard in
          if Options.disallow_unification_guards ()
          && not allow_guards
          && NonTrivial? guard.guard_f
          then (
            fail_doc [
              text "Could not typecheck unifier solved implicit" ^/^ pp u.ctx_uvar_head ^/^
              text "to" ^/^ pp sol ^/^ text "since it produced a guard and guards were not allowed";
              text "Guard =" ^/^ pp g
            ]
          )
          else (
            proc_guard' false "guard for implicit" env guard (Some guard_tok) (Some sc) u.ctx_uvar_range ;!
            mark_uvar_as_already_checked u;
            return ()
          )

        | Inr failed ->
          fail_doc [
            text "Could not typecheck unifier solved implicit" ^/^ pp u.ctx_uvar_head ^/^
            text "to" ^/^ pp sol ^/^ text "because" ^/^ doc_of_string (Core.print_error failed)
          ]
  in
  if env.phase1 //phase1 is untrusted
  then return ()
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
      Format.print2 "%%%%%%%%do_unify %s =? %s\n" (show t1)
                                              (show t2);

    let all_uvars =
      (match check_side with
       | Check_none -> empty ()
       | Check_left_only -> Free.uvars t1
       | Check_right_only -> Free.uvars t2
       | Check_both -> union (Free.uvars t1) (Free.uvars t2))
      |> elems /// GGG order dependent but does not seem too bad
    in

    match!
      catch (//restore UF graph in case anything fails
        let! gopt = trytac cur_goal in
        try
          let res =
            if allow_guards
            then Rel.try_teq true env t1 t2
            else Rel.teq_nosmt env t1 t2
          in
          if dbg then
            Format.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                              (FStarC.Common.string_of_option (Rel.guard_to_string env) res)
                              (show t1)
                              (show t2);

          match res with
          | None ->
            return None
          | Some g ->
            tc_unifier_solved_implicits env must_tot allow_guards all_uvars;!
            add_implicits (Listlike.to_list g.implicits);!
            return (Some g)

        with | Errors.Error (_, msg, r, _) ->
               log (fun () -> Format.print2 ">> do_unify error, (%s) at (%s)\n" (Errors.rendermsg msg) (show r));!
               return None
      )
    with
    | Inl exn -> traise exn
    | Inr v -> return v

(* Just a wrapper over __do_unify_wflags to better debug *)
let __do_unify
  (allow_guards:bool)
  (must_tot:bool)
  (check_side:check_unifier_solved_implicits_side)
  (env:env) (t1:term) (t2:term)
  : tac (option guard_t) =
  return ();!
  if !dbg_TacUnify then begin
    Options.push ();
    let _ = Options.set_options "--debug Rel,RelCheck" in
    ()
  end;
  let! r = __do_unify_wflags !dbg_TacUnify allow_guards must_tot check_side env t1 t2 in
  if !dbg_TacUnify then Options.pop ();
  return r

(* SMT-free unification. *)
let do_unify_aux
  (must_tot:bool)
  (check_side:check_unifier_solved_implicits_side)
  (env:env) (t1:term) (t2:term)
  : tac bool =
  match! __do_unify false must_tot check_side env t1 t2 with
  | None -> return false
  | Some g ->
    (* g has to be trivial and we have already added its implicits *)
    if not (Env.is_trivial_guard_formula g) then
      failwith "internal error: do_unify: guard is not trivial"
    else
      return ();!
    return true

let do_unify (must_tot:bool) (env:env) (t1:term) (t2:term) : tac bool =
  do_unify_aux must_tot Check_both env t1 t2

let do_unify_maybe_guards (allow_guards:bool) (must_tot:bool)
  (env:env) (t1:term) (t2:term)
  : tac (option guard_t) =
  __do_unify allow_guards must_tot Check_both env t1 t2

(* Does t1 match t2? That is, do they unify without instantiating/changing t1? *)
let do_match (must_tot:bool) (env:Env.env) (t1:term) (t2:term) : tac bool =
  let! tx = mk_tac (fun ps -> let tx = UF.new_transaction () in
                              Success (tx, ps)) in
  let uvs1 = SF.uvars_uncached t1 in
  let! r = do_unify_aux must_tot Check_right_only env t1 t2 in
  if r then begin
      let uvs2 = SF.uvars_uncached t1 in
      if not (equal uvs1 uvs2)
      then (UF.rollback tx; return false)
      else return true
  end
  else return false

(* This is a bandaid. It's similar to do_match but checks that the
LHS of the equality in [t1] is not instantiated, but the RHS might be.
It is a pain to expose the whole logic to tactics, so we just do it
here for now. *)
let do_match_on_lhs (must_tot:bool) (env:Env.env) (t1:term) (t2:term) : tac bool =
  let! tx = mk_tac (fun ps -> let tx = UF.new_transaction () in
                              Success (tx, ps)) in
  match destruct_eq env t1 with
  | None -> fail "do_match_on_lhs: not an eq"
  | Some (lhs, _) ->
    let uvs1 = SF.uvars_uncached lhs in
    let! r = do_unify_aux must_tot Check_right_only env t1 t2 in
    if r then begin
        let uvs2 = SF.uvars_uncached lhs in
        if not (equal uvs1 uvs2)
        then (UF.rollback tx; return false)
        else return true
    end
    else return false

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
      fail (Format.fmt1 "Goal %s is already solved" (goal_to_string_verbose goal))
    | None ->
      FStarC.Syntax.Unionfind.change goal.goal_ctx_uvar.ctx_uvar_head solution;
      mark_goal_implicit_already_checked goal;
      return ()

let trysolve (goal : goal) (solution : term) : tac bool =
  let must_tot = true in
  do_unify must_tot (goal_env goal) solution (goal_witness goal)

let solve (goal : goal) (solution : term) : tac unit =
    let e = goal_env goal in
    log (fun () -> Format.print2 "solve %s := %s\n" (show (goal_witness goal)) (show solution));!
    let! b = trysolve goal solution in
    if b
    then (dismiss;! remove_solved_goals)
    else
      fail_doc [
        ttd (goal_env goal) solution ^/^
        text "does not solve" ^/^
        ttd (goal_env goal) (goal_witness goal) ^/^ text ":" ^/^ ttd (goal_env goal) (goal_type goal)
      ]

let solve' (goal : goal) (solution : term) : tac unit =
  set_solution goal solution;!
  dismiss;!
  remove_solved_goals

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

let meas (s:string) (f : tac 'a) : tac 'a =
  mk_tac (fun ps ->
    let (r, ms) = Timing.record_ms (fun () -> Tactics.Monad.run f ps) in
    Format.print2 "++ Tactic %s ran in \t\t%sms\n" s (show ms);
    r)

(* Nuclear option to benchmark every primitive. *)
(* let wrap_err s f = meas s (wrap_err s f) *)

let tadmit_t (t:term) : tac unit = wrap_err "tadmit_t" <| (
  let! ps = get in
  let! g = cur_goal in
  // should somehow taint the state instead of just printing a warning
  let open FStarC.Errors.Msg in
  let open FStarC.Pprint in
  Err.log_issue (pos (goal_type g)) Errors.Warning_TacAdmit [
      text "Tactics admitted goal.";
      prefix 2 1 (text "Goal")
                 (arbitrary_string <| goal_to_string "" None ps g);
    ];
  solve' g t)

let fresh () : tac int =
  let! ps = get in
  let n = ps.freshness in
  let ps = { ps with freshness = n + 1 } in
  set ps;!
  return n

let curms () : tac int =
    return (Time.get_time_of_day_ms ())

(* Annoying duplication here *)
let __tc (e : env) (t : term) : tac (term & typ & guard_t) =
    let! ps = get in
    log (fun () -> Format.print1 "Tac> __tc(%s)\n" (show t));!
    return (TcTerm.typeof_tot_or_gtot_term e t true)

let __tc_ghost (e : env) (t : term) : tac (term & typ & guard_t) =
    let! ps = get in
    log (fun () -> Format.print1 "Tac> __tc_ghost(%s)\n" (show t));!
    let e = {e with letrecs=[]} in
    let t, lc, g = TcTerm.tc_tot_or_gtot_term e t in
    return (t, lc.res_typ, g)

let __tc_lax (e : env) (t : term) : tac (term & lcomp & guard_t) =
    let! ps = get in
    log (fun () -> Format.print2 "Tac> __tc_lax(%s)(Context:%s)\n"
                           (show t)
                           (Env.all_binders e |> show));!
    let e = {e with admit = true} in
    let e = {e with letrecs=[]} in
    return (TcTerm.tc_term e t)

let tcc (e : env) (t : term) : tac comp = wrap_err "tcc" <| (
  let! (_, lc, _) = __tc_lax e t in
  (* Why lax? What about the guard? It doesn't matter! tc is only
   * a way for metaprograms to query the typechecker, but
   * the result has no effect on the proofstate and nor is it
   * taken for a fact that the typing is correct. *)
  return (TcComm.lcomp_comp lc |> fst)  //dropping the guard from lcomp_comp too!
)

let tc (e : env) (t : term) : tac typ = wrap_err "tc" <| (
  let! c = tcc e t in
  return (U.comp_result c)
)

(* Applies t to each of the current goals
      fails if t fails on any of the goals
      collects each result in the output list *)
let rec map (tau:tac 'a): tac (list 'a) =
  let! ps = get in
  match ps.goals with
  | [] -> return []
  | _::_ ->
    let! (h,t) = divide 1 tau (map tau) in
    return (h :: t)

(* Applies t1 to the current head goal
   And t2 to all the the sub-goals produced by t1

   Collects the resulting goals of t2 along with the initial auxiliary goals
 *)
let seq (t1:tac unit) (t2:tac unit) : tac unit =
  focus (t1 ;! map t2 ;! return ())

let should_check_goal_uvar (g:goal) = U.ctx_uvar_should_check g.goal_ctx_uvar

let bnorm_and_replace g = replace_cur (bnorm_goal g)

let bv_to_binding (bv : bv) : RD.binding =
  {
    uniq   = bv.index;
    sort   = bv.sort;
    ppname = Sealed.seal (show bv.ppname);
  }

let binder_to_binding (b:binder) : RD.binding =
  bv_to_binding b.binder_bv

let binding_to_string (b : RD.binding) : string =
  Sealed.unseal b.ppname ^ "#" ^ show b.uniq


let binding_to_bv (b : RD.binding) : bv =
  {
    sort = b.sort;
    ppname = mk_ident (Sealed.unseal b.ppname, Range.dummyRange);
    index = b.uniq;
  }

let binding_to_binder (b:RD.binding) : S.binder =
  let bv = binding_to_bv b in
  S.mk_binder bv

let arrow_one (env:Env.env) (t:term) =
  match U.arrow_one_ln t with
  | None -> None
  | Some (b, c) ->
    let env, [b], c = FStarC.TypeChecker.Core.open_binders_in_comp env [b] c in
    Some (env, b, c)

let arrow_one_whnf (env:Env.env) (t:term) =
  match arrow_one env t with
  | Some r -> Some r
  | None -> arrow_one env (whnf env t)

(*
  [intro]:

  Initial goal: G |- ?u : (t -> t')

  Now we do an `intro`:

  Next goal:  `G, x:t |- ?v : t'`

  with `?u := (fun (x:t) -> ?v @ [NM(x, 0)])`
*)
let intro () : tac RD.binding = wrap_err "intro" <| (
    let! goal = cur_goal in
    match arrow_one_whnf (goal_env goal) (goal_type goal) with
    | Some (_, _, c) when not (U.is_total_comp c) ->
        fail "Codomain is effectful"

    | Some (env', b, c) ->
        let typ' = U.comp_result c in
        //Format.print1 "[intro]: current goal is %s" (goal_to_string goal);
        //Format.print1 "[intro]: current goal witness is %s" (show (goal_witness goal));
        //Format.print1 "[intro]: with goal type %s" (show (goal_type goal));
        //Format.print2 "[intro]: with binder = %s, new goal = %s"
        //         (Print.binders_to_string ", " [b])
        //         (show typ');
        let! body, ctx_uvar =
          new_uvar "intro" env' typ'
                   (Some (should_check_goal_uvar goal))
                   (goal_typedness_deps goal)
                   (rangeof goal) in
        let sol = U.abs [b] body (Some (U.residual_comp_of_comp c)) in
        //Format.print1 "[intro]: solution is %s"
        //           (show sol);
        //Format.print1 "[intro]: old goal is %s" (goal_to_string goal);
        //Format.print1 "[intro]: new goal is %s"
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
        replace_cur g ;!
        return (binder_to_binding b)
    | None ->
        fail1 "goal is not an arrow (%s)" (tts (goal_env goal) (goal_type goal))
    )

(* As [intro], but will introduce n binders at once when the expected type is a
literal arrow. *)
let intros (max:int) : tac (list RD.binding) = wrap_err "intros" <| (
    let! goal = cur_goal in
    let bs, c = U.arrow_formals_comp_ln (goal_type goal) in
    let bs, c =
      (* if user specified a max, maybe trim the bs list and repackage into c *)
      if max >= 0
      then (
        let bs0, bs1 = List.splitAt max bs in
        let c = S.mk_Total (U.arrow_ln bs1 c) in
        bs0, c
      ) else bs, c
    in
    let env', bs, c = FStarC.TypeChecker.Core.open_binders_in_comp (goal_env goal) bs c in
    if not (U.is_pure_comp c) then
      fail ("Codomain is effectful: " ^ show c)
    else return ();!
    let typ' = U.comp_result c in
    let! body, ctx_uvar =
      new_uvar "intros" env' typ'
               (Some (should_check_goal_uvar goal))
               (goal_typedness_deps goal)
               (rangeof goal) in
    let sol = U.abs bs body (Some (U.residual_comp_of_comp c)) in
    set_solution goal sol ;!
    let g = mk_goal env' ctx_uvar goal.opts goal.is_guard goal.label in
    replace_cur g ;!
    return (List.map binder_to_binding bs)
)

// TODO: missing: precedes clause, and somehow disabling fixpoints only as needed
let intro_rec () : tac (RD.binding & RD.binding) =
    let! goal = cur_goal in
    Format.print_string "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
    Format.print_string "WARNING (intro_rec): proceed at your own risk...\n";
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
             return (binder_to_binding (S.mk_binder bv), binder_to_binding b)
    | None ->
        fail1 "intro_rec: goal is not an arrow (%s)" (tts (goal_env goal) (goal_type goal))

let norm (s : list NormSteps.norm_step) : tac unit =
    let! goal = cur_goal in
    if_verbose (fun () -> Format.print1 "norm: witness = %s\n" (show (goal_witness goal))) ;!
    // Translate to actual normalizer steps
    let steps = [Env.Reify; Env.DontUnfoldAttr [PC.tac_opaque_attr]]@(Cfg.translate_norm_steps s) in
    //let w = normalize steps (goal_env goal) (goal_witness goal) in
    let t = normalize steps (goal_env goal) (goal_type goal) in
    replace_cur (goal_with_type goal t)

let __norm_term_env
  (well_typed:bool) (e : env) (s : list NormSteps.norm_step) (t : term)
  : tac term
= wrap_err "norm_term" <| (
    let! ps = get in
    if_verbose (fun () -> Format.print1 "norm_term_env: t = %s\n" (show t)) ;!
    // only for elaborating lifts and all that, we don't care if it's actually well-typed
    let! t =
      if well_typed
      then return t
      else let! t, _, _ = __tc_lax e t in return t
    in
    let steps = [Env.Reify; Env.DontUnfoldAttr [PC.tac_opaque_attr]]@(Cfg.translate_norm_steps s) in
    let t = normalize steps ps.main_context t in
    if_verbose (fun () -> Format.print1 "norm_term_env: t' = %s\n" (show t)) ;!
    return t
    )

let norm_term_env e s t = __norm_term_env false e s t
let refl_norm_well_typed_term e s t = __norm_term_env true e s t

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
    let env = {env with uvar_subtyping=false} in
    let! t, typ, guard = __tc env t in
    if_verbose (fun () -> Format.print2 "__exact_now: got type %s\n__exact_now: and guard %s\n"
                                                     (show typ)
                                                     (Rel.guard_to_string (goal_env goal) guard)) ;!
    proc_guard "__exact typing" (goal_env goal) guard None (Some (should_check_goal_uvar goal)) (rangeof goal) ;!
    if_verbose (fun () -> Format.print2 "__exact_now: unifying %s and %s\n" (show typ)
                                                                  (show (goal_type goal))) ;!
    let! b = do_unify true (goal_env goal) typ (goal_type goal) in
    if b
    then ( // do unify succeeded with a trivial guard; so the goal is solved and we don't have to check it again
      mark_goal_implicit_already_checked goal;
      solve goal t
    )
    else
      let typ, goalt = TypeChecker.Err.print_discrepancy (ttd (goal_env goal)) typ (goal_type goal) in
      fail_doc [
        prefix 2 1 (text "Term") (ttd (goal_env goal) t) ^/^
        prefix 2 1 (text "of type") typ ^/^
        prefix 2 1 (text "does not exactly solve the goal") goalt;
      ]

let t_exact try_refine set_expected_typ tm : tac unit = wrap_err "exact" <| (
    if_verbose (fun () -> Format.print1 "t_exact: tm = %s\n" (show tm)) ;!
    match! catch (__exact_now set_expected_typ tm) with
    | Inr r -> return r
    | Inl e when not (try_refine) -> traise e
    | Inl e ->
      if_verbose (fun () -> Format.print_string "__exact_now failed, trying refine...\n") ;!
      match! catch (norm [NormSteps.Delta] ;! refine_intro () ;! __exact_now set_expected_typ tm) with
      | Inr r ->
        if_verbose (fun () -> Format.print_string "__exact_now: failed after refining too\n") ;!
        return r
      | Inl _ ->
        if_verbose (fun () -> Format.print_string "__exact_now: was not a refinement\n") ;!
        traise e)

(* Can t1 unify t2 if it's applied to arguments? If so return uvars for them *)
(* NB: Result is reversed, which helps so we use fold_right instead of fold_left *)
let try_unify_by_application (should_check:option should_check_uvar)
                             (only_match:bool)
                             (e : env)
                             (ty1 : term)
                             (ty2 : term)
                             (rng:Range.t)
   : tac (list (term & aqual & ctx_uvar))
   = let f = if only_match then do_match else do_unify in
     let must_tot = true in
     let rec aux (acc : list (term & aqual & ctx_uvar))
                 (typedness_deps : list ctx_uvar) //map proj_3 acc
                 (ty1:term)
        : tac (list (term & aqual & ctx_uvar))
        = match! f must_tot e ty2 ty1 with
          | true -> return acc (* Done! *)
          | false ->
            (* Not a match, try instantiating the first type by application *)
            match U.arrow_one ty1 with
            | None ->
              fail_doc [
                prefix 2 1 (text "Could not instantiate")
                  (ttd e ty1) ^/^
                prefix 2 1 (text "to")
                  (ttd e ty2)
              ]

            | Some (b, c) ->
              if not (U.is_total_comp c) then fail "Codomain is effectful" else
              let! uvt, uv = new_uvar "apply arg" e b.binder_bv.sort should_check typedness_deps rng in
              if_verbose (fun () -> Format.print1 "t_apply: generated uvar %s\n" (show uv)) ;!
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
      return #tac [gl] // FIXME: inference failure!
    | _ ->
      //
      // This implicits has already been solved
      // We would have typechecked its solution already,
      //   just after the Rel call
      //
      return []
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
      (fun () -> Format.print4 "t_apply: uopt %s, only_match %s, tc_resolved_uvars %s, tm = %s\n"
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
      (fun () -> Format.print5 "t_apply: tm = %s\nt_apply: goal = %s\nenv.gamma=%s\ntyp=%s\nguard=%s\n"
                        (show tm)
                        (goal_to_string_verbose goal)
                        (show e.gamma)
                        (show typ)
                        (Rel.guard_to_string e guard)) ;!
    // Focus helps keep the goal order
    let typ = bnorm e typ in
    if only_match && not (is_empty (Free.uvars_uncached typ)) then
      fail "t_apply: only_match is on, but the type of the term to apply is not a uvar"
    else return ();!
    let! uvs = try_unify_by_application (Some should_check) only_match e typ (goal_type goal) (rangeof goal) in
    if_verbose
      (fun () -> Format.print1 "t_apply: found args = %s\n"
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
    proc_guard "apply guard" e guard None (Some should_check) (rangeof goal)
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
        Option.map (fun post -> (U.t_true, post)) (U.un_squash res)
    else
        None

let t_apply_lemma (noinst:bool) (noinst_lhs:bool)
                  (tm:term) : tac unit = wrap_err "apply_lemma" <| focus (
    let! ps = get in
    if_verbose (fun () -> Format.print1 "apply_lemma: tm = %s\n" (show tm)) ;!
    let is_unit_t t =
      match (SS.compress t).n with
      | Tm_fvar fv when S.fv_eq_lid fv PC.unit_lid -> true
      | _ -> false
    in
    let! goal = cur_goal in
    let env = goal_env goal in
    Tactics.Monad.register_goal goal;
    let! tm, t, guard =
      let env = {env with uvar_subtyping=false} in
      __tc env tm
    in
    let bs, comp = U.arrow_formals_comp t in
    match lemma_or_sq comp with
    | None ->
      fail_doc [
        prefix 2 1 (text "Term to apply has computation type:") (pp comp);
        text "`apply_lemma` can only apply functions with the Lemma effect or returning a squashed value.";
      ]

    | Some (pre, post) ->
      let! uvs, _, implicits, subst =
        foldM_left
          (fun (uvs, deps, imps, subst) ({binder_bv=b;binder_qual=aq}) ->
               let b_t = SS.subst subst b.sort in
               if is_unit_t b_t
               then
                   // Simplification: if the argument is simply unit, then don't ask for it
                   return <| ((U.exp_unit, aq)::uvs, deps, imps, S.NT(b, U.exp_unit)::subst)
               else
                   let! t, u = new_uvar "apply_lemma" env b_t
                     (goal
                      |> should_check_goal_uvar
                      |> (function | Strict -> Allow_ghost "apply lemma uvar"
                                  | x -> x)
                      |> Some)
                     deps
                     (rangeof goal) in
                   if !dbg_2635
                   then
                     Format.print2 "Apply lemma created a new uvar %s while applying %s\n"
                       (show u)
                       (show tm);
                   return ((t, aq)::uvs, u::deps, (t, u)::imps, S.NT(b, t)::subst))
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
        let open FStarC.Class.PP in
        let open FStarC.Pprint in
        let open FStarC.Errors.Msg in
        // let post, goalt = TypeChecker.Err.print_discrepancy (tts env)
        //                                                     (U.mk_squash post_u post)
        //                                                     (goal_type goal) in
        fail_doc [
          prefix 2 1 (text "Cannot instantiate lemma:") (pp tm) ^/^
          prefix 2 1 (text "with postcondition:") (N.term_to_doc env post) ^/^
          prefix 2 1 (text "to match goal:") (pp (goal_type goal))
        ]
      )
      else (
        // We solve with (), we don't care about the witness if applying a lemma
        let goal_sc = should_check_goal_uvar goal in
        solve' goal U.exp_unit ;!
        let is_free_uvar uv t =
            for_any (fun u -> UF.equiv u.ctx_uvar_head uv) (SF.uvars t)
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
        proc_guard "apply_lemma guard" env guard None (Some goal_sc) (rangeof goal) ;!
        let pre_u = env.universe_of env pre in
        (match Env.check_trivial (Rel.simplify_vc false env pre) with
         | Trivial -> return ()
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
            else Option.map (fun (e'', bv, bvs) -> (e'', bv, bv'::bvs )) (aux e') 
    in
    Option.map (fun (e', bv, bvs) -> (e', bv, List.rev bvs)) (aux e)

let rewrite (hh:RD.binding) : tac unit = wrap_err "rewrite" <| (
    let! goal = cur_goal in
    let h = binding_to_binder hh in
    let bv = h.binder_bv in
    if_verbose (fun _ -> Format.print2 "+++Rewrite %s : %s\n" (show bv) (show bv.sort)) ;!
    match split_env bv (goal_env goal) with
    | None -> 
      fail "binder not found in environment"
    | Some (e0, bv, bvs) ->
      begin
      match destruct_eq e0 bv.sort with
      | Some (x, e) ->
        begin
        match (SS.compress x).n with
        | Tm_name x ->
          let s = [NT(x, e)] in

          let t = goal_type goal in
          let bs = List.map S.mk_binder bvs in

          let bs', t' = SS.subst_binders s bs, SS.subst s t in
          let e0 = Env.push_bvs e0 [bv] in
          let new_env = Env.push_binders e0 bs' in

          let! uvt, uv =
               new_uvar "rewrite" new_env t'
                           (Some (should_check_goal_uvar goal))
                           (goal_typedness_deps goal)
                           (rangeof goal)
          in
          let goal' = mk_goal new_env uv goal.opts goal.is_guard goal.label in
          set_solution goal uvt ;!
          replace_cur goal'

        | _ ->
          fail "Not an equality hypothesis with a variable on the LHS"
        end
      | _ -> fail "Not an equality hypothesis"
      end
    )

let replace (t1 t2 : term) (s : term) : term =
  Syntax.Visit.visit_term false (fun t ->
    if U.term_eq t t1
    then t2
    else t) s

let grewrite (t1 t2 : term) : tac unit = wrap_err "grewrite" <| (focus (
    let! goal = cur_goal in
    let goal_t = goal_type goal in
    let env = goal_env goal in
    let! t1, typ1, g1  = __tc env t1 in
    let! t2, typ2, g2  = __tc env t2 in

    (* Remove top level refinements. We just need to create an equality between t1 and t2,,
    one of them could have a refined type and that should not matter. *)
    let typ1' = N.unfold_whnf' [Env.Unrefine] env typ1 in
    let typ2' = N.unfold_whnf' [Env.Unrefine] env typ2 in
    if! do_unify false env typ1' typ2' then
      return ()
    else (
      fail_doc [
        text "Types do not match for grewrite";
        text "Type of" ^/^ parens (pp t1) ^/^ equals ^/^ pp typ1;
        text "Type of" ^/^ parens (pp t2) ^/^ equals ^/^ pp typ2;
      ]
    );!
    let u = env.universe_of env typ1 in
    let goal_t' = replace t1 t2 goal_t in

    let! g_eq =
      (* However, retain the original, possibly refined, of t1 for this equality. *)
      mk_irrelevant_goal "grewrite.eq" env (U.mk_eq2 u typ1 t1 t2) None
        goal.goal_ctx_uvar.ctx_uvar_range goal.opts goal.label
    in

    replace_cur (goal_with_type goal goal_t');!
    push_goals [g_eq];!

    return ()
))

let rename_to (b : RD.binding) (s : string) : tac RD.binding = 
  let subst_goal (b1 : bv) (b2 : bv) (g:goal) : tac (option goal) =
      match split_env b1 (goal_env g) with
      | Some (e0, b1, bvs) ->
          let bs = List.map S.mk_binder bvs in

          let t = goal_type g in

          let subst = [S.NT (b1, S.bv_to_name b2)] in
          let bs' = SS.subst_binders subst bs in
          let t' = SS.subst subst t in

          let new_env = Env.push_binders e0 (S.mk_binder b2 :: bs') in

          (* Make a new goal in the new env (with new binders) *)
          let! uvt, uv = new_uvar "subst_goal" new_env t'
                                (Some (should_check_goal_uvar g))
                                (goal_typedness_deps g)
                                (rangeof g) in

          let goal' = mk_goal new_env uv g.opts g.is_guard g.label in

          set_solution g uvt ;!

          return (Some goal')

      | None ->
          return None
  in
  wrap_err "rename_to" <| (
    let! goal = cur_goal in
    let bv = binding_to_bv b in
    let bv' = ({ bv with ppname = mk_ident (s, (range_of_id bv.ppname)) }) in
    match! subst_goal bv bv' goal with
    | None -> fail "binder not found in environment"
    | Some goal ->
      replace_cur goal ;!
      return { b with RD.ppname = Sealed.seal s}
    )

let var_retype (b : RD.binding) : tac unit = wrap_err "binder_retype" <| (
    let! goal = cur_goal in
    let bv = binding_to_bv b in
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

let norm_binding_type (s : list NormSteps.norm_step) (b : RD.binding) : tac unit = wrap_err "norm_binding_type" <| (
    let! goal = cur_goal in
    let bv = binding_to_bv b in
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

let clear (b : RD.binding) : tac unit =
    let bv = binding_to_bv b in
    let! goal = cur_goal in
    if_verbose (fun () -> Format.print2 "Clear of (%s), env has %s binders\n"
                        (binding_to_string b)
                        (Env.all_binders (goal_env goal) |> List.length |> show)) ;!
    match split_env bv (goal_env goal) with
    | None -> fail "Cannot clear; binder not in environment"
    | Some (e', bv, bvs) ->
      let rec check bvs =
          match bvs with
          | [] -> return ()
          | bv'::bvs ->
            if free_in bv bv'.sort
            then fail (Format.fmt1 "Cannot clear; binder present in the type of %s"
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
    | Some (x, _) -> clear (bv_to_binding x) // we ignore the qualifier anyway

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
      let uvars = FStarC.Syntax.Free.uvars t in
      if for_all is_uvar_untyped_or_already_checked uvars
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
            match Core.compute_term_type env t with
            | Inr _ -> false
            | Inl (_, t_ty, guard) -> (  // ignoring effect, ghost is ok
              FStarC.TypeChecker.Core.commit_guard_and_tok_opt guard; //intentionally admit guard; goal is well-typed
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
    | None -> return false
    | Some guard ->
      solve' g U.exp_unit ;!
      if allow_guards
      then
        let! goal = goal_of_guard "t_trefl" (goal_env g) (guard_formula guard) (Some should_check) (rangeof g) in
        push_goals [goal] ;!
        return true
      else
        // If allow_guards is false, this guard must be trivial and we don't
        // add it, but we check its triviality for sanity.
        if Env.is_trivial_guard_formula guard
        then return true
        else failwith "internal error: _t_refl: guard is not trivial"
  in
  match! attempt l r with
  | true -> return ()
  | false ->
    (* if that didn't work, normalize and retry *)
    let norm = N.normalize [Env.UnfoldUntil delta_constant; Env.Primops; Env.DontUnfoldAttr [PC.tac_opaque_attr]] (goal_env g) in
    match! attempt (norm l) (norm r) with
    | true -> return ()
    | false ->
      let ls, rs = TypeChecker.Err.print_discrepancy (tts (goal_env g)) l r in
      fail2 "cannot unify (%s) and (%s)" ls rs

let t_trefl (allow_guards:bool) : tac unit = wrap_err "t_trefl" <| (
  let! g = cur_goal in
  match destruct_eq (goal_env g) (goal_type g) with
  | Some (l, r) ->
    _t_trefl allow_guards l r
  | None ->
    fail_doc [
      text "Not an equality:" ^/^ ttd (goal_env g) (goal_type g);
    ]
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

// longest_prefix f l1 l2 = (p, r1, r2) ==> l1 = p@r1 /\ l2 = p@r2 ;   and p is maximal
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

let eq_binding b1 b2 =
    match b1, b2 with
    | _ -> false
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

    let ng = U.mk_conj t1 t2 in
    let nenv = { goal_env g1 with gamma = List.rev gamma } in
    let! goal = mk_irrelevant_goal "joined" nenv ng goal_sc (rangeof g1) g1.opts g1.label in
    if_verbose (fun () -> Format.print3 "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                         (goal_to_string_verbose g1)
                         (goal_to_string_verbose g2)
                         (goal_to_string_verbose goal)) ;!
    set_solution g1 U.exp_unit ;!
    set_solution g2 U.exp_unit ;!
    return goal

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
    )

let top_env     () : tac env  = let! ps = get in return <| ps.main_context

let lax_on () : tac bool =
  (* Check the goal if any??? *)
  let! ps = get in
  return ps.main_context.admit

let unquote (ty : term) (tm : term) : tac term = wrap_err "unquote" <| (
    if_verbose (fun () -> Format.print1 "unquote: tm = %s\n" (show tm)) ;!
    let! goal = cur_goal in
    let env = Env.set_expected_typ (goal_env goal) ty in
    let! tm, typ, guard = __tc_ghost env tm in
    if_verbose (fun () -> Format.print1 "unquote: tm' = %s\n" (show tm)) ;!
    if_verbose (fun () -> Format.print1 "unquote: typ = %s\n" (show typ)) ;!
    proc_guard "unquote" env guard None (Some (should_check_goal_uvar goal)) (rangeof goal) ;!
    return tm
    )

let uvar_env (env : env) (ty : option typ) : tac term =
  wrap_err "uvar_env" <| (
  let! ps = get in
  // If no type was given, add a uvar for it too!
  let! typ, g, r =
    match ty with
    | Some ty ->
      let env = Env.set_expected_typ env (U.type_u () |> fst) in
      let! ty, _, g = __tc_ghost env ty in
      return (ty, g, ty.pos)

    | None ->
      //the type of this uvar is just Type; so it's typedness deps is []
      let! typ, uvar_typ = new_uvar "uvar_env.2" env (fst <| U.type_u ()) None [] ps.entry_range in
      return (typ, Env.trivial_guard, Range.dummyRange)
  in
  proc_guard "uvar_env_typ" env g None None r;!
  //the guard is an explicit goal; so the typedness deps of this new uvar is []
  let! t, uvar_t = new_uvar "uvar_env" env typ None [] ps.entry_range in
  return t
  )

let ghost_uvar_env (env : env) (ty : typ) : tac term =
  let! ps = get in
  // If no type was given, add a uvar for it too!
  let! typ, _, g = __tc_ghost env ty in
  proc_guard "ghost_uvar_env_typ" env g None None ty.pos ;!
  //the guard is an explicit goal; so the typedness deps of this new uvar is []
  let! t, uvar_t = new_uvar "uvar_env" env typ (Some (Allow_ghost "User ghost uvar")) [] ps.entry_range in
  return t

let fresh_universe_uvar () : tac term =
  U.type_u () |> fst |> return

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

let match_env (e:env) (t1 : term) (t2 : term) : tac bool =
  wrap_err "match_env" <|
  default_if_err false <| (
  let! ps = get in
  let! t1, ty1, g1 = __tc e t1 in
  let! t2, ty2, g2 = __tc e t2 in
  proc_guard "match_env g1" e g1 None None ps.entry_range ;!
  proc_guard "match_env g2" e g2 None None ps.entry_range ;!
  let must_tot = true in
    tac_and (do_match must_tot e ty1 ty2)
            (do_match must_tot e t1 t2)
  )

let unify_env (e:env) (t1 : term) (t2 : term) : tac bool =
  wrap_err "unify_env" <|
  default_if_err false <| (
  let! ps = get in
  let! t1, ty1, g1 = __tc e t1 in
  let! t2, ty2, g2 = __tc e t2 in
  proc_guard "unify_env g1" e g1 None None ps.entry_range ;!
  proc_guard "unify_env g2" e g2 None None ps.entry_range ;!
  let must_tot = true in
    tac_and (do_unify must_tot e ty1 ty2)
            (do_unify must_tot e t1 t2)
  )

let unify_guard_env (e:env) (t1 : term) (t2 : term) : tac bool = wrap_err "unify_guard_env" <| (
    let! ps = get in
    let! t1, ty1, g1 = __tc e t1 in
    let! t2, ty2, g2 = __tc e t2 in
    proc_guard "unify_guard_env g1" e g1 None None ps.entry_range ;!
    proc_guard "unify_guard_env g2" e g2 None None ps.entry_range ;!
    let must_tot = true in
    match! do_unify_maybe_guards true must_tot e ty1 ty2 with
    | None -> return false
    | Some g1 ->
      match! do_unify_maybe_guards true must_tot e t1 t2 with
      | None -> return false
      | Some g2 ->
        let formula : term = U.mk_conj (guard_formula g1) (guard_formula g2) in
        let! goal = goal_of_guard "unify_guard_env.g2" e formula None ps.entry_range in
        push_goals [goal] ;!
        return true
    )

let launch_process (prog : string) (args : list string) (input : string) : tac string =
    // The `bind return ()` thunks the tactic
    return ();!
    if Options.unsafe_tactic_exec () then
        let s = BU.run_process "tactic_launch" prog args (Some input) in
        return s
    else
        fail "launch_process: will not run anything unless --unsafe_tactic_exec is provided"

let fresh_bv_named (nm : string) : tac bv =
  // The `bind return ()` thunks the tactic. Not really needed, just being paranoid
  return ();! return (gen_bv nm None S.tun)

let change (ty : typ) : tac unit = wrap_err "change" <| (
    if_verbose (fun () -> Format.print1 "change: ty = %s\n" (show ty)) ;!
    let! g = cur_goal in
    let! ty, _, guard = __tc (goal_env g) ty in
    proc_guard "change" (goal_env g) guard None (Some (should_check_goal_uvar g)) (rangeof g) ;!
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
    else return ()

let t_destruct (s_tm : term) : tac (list (fv & int)) = wrap_err "destruct" <| (
    let! g = cur_goal in
    let! s_tm, s_ty, guard = __tc (goal_env g) s_tm in
    proc_guard "destruct" (goal_env g) guard None (Some (should_check_goal_uvar g)) (rangeof g) ;!
    let s_ty = N.normalize [Env.DontUnfoldAttr [PC.tac_opaque_attr]; Env.Weak; Env.HNF; Env.UnfoldUntil delta_constant]
                           (goal_env g) s_ty in
    let h, args = U.head_and_args_full (U.unrefine s_ty) in
    let! fv, a_us =
         match (SS.compress h).n with
         | Tm_fvar fv -> return (fv, [])
         | Tm_uinst (h', us) ->
           begin match (SS.compress h').n with
           | Tm_fvar fv -> return (fv, us)
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
                        (* Format.print2 "ty of %s = %s\n" (show c_lid) *)
                        (*                             (show c_ty); *)
                        (* Make sure to preserve qualifiers if possible.
                        This is mostly so we retain Record_projector quals, which
                        are meaningful for extraction. *)
                        let qual =
                          let fallback () = Some Data_ctor in
                          let qninfo = Env.lookup_qname (goal_env g) c_lid in
                          match qninfo with
                          | Some (Inr (se, _us), _rng) ->
                              Syntax.DsEnv.fv_qual_of_se se
                          | _ ->
                              fallback ()
                        in
                        let fv = S.lid_as_fv c_lid qual in

                        failwhen (List.length a_us <> List.length c_us) "t_us don't match?" ;!
                        let s = Env.mk_univ_subst c_us a_us in
                        let c_ty = SS.subst s c_ty in

                        (* The constructor might be universe-polymorphic, just use
                         * fresh univ_uvars for its universes. *)
                        let c_us, c_ty = Env.inst_tscheme (c_us, c_ty) in

                        (* Format.print2 "ty(2) of %s = %s\n" (show c_lid) *)
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

                        (* Format.print1 "bs = (%s)\n" (Print.binders_to_string ", " bs); *)
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
                        return (g', br, (fv, (List.length bs <: int)))
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
      return infos

    | _ -> fail "not an inductive type"
    )

let gather_explicit_guards_for_resolved_goals ()
  : tac unit
  = return ()

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

let set_urgency (u:int) : tac unit =
    let! ps = get in
    let ps = { ps with urgency = u } in
    set ps

let set_dump_on_failure (b:bool) : tac unit =
    let! ps = get in
    let ps = { ps with dump_on_failure = b } in
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
      let lopt' = lopt |> Option.map (fun rc -> {rc with residual_typ=
        rc.residual_typ |> Option.map (fun t ->
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
    let frag_of_text s = { frag_fname= "<string_of_term>"
                         ; frag_line = 1 ; frag_col  = 0
                         ; frag_text = s } in
    match parse None (Fragment (frag_of_text s)) with
    | Term t ->
      let dsenv = FStarC.Syntax.DsEnv.set_current_module e.dsenv (current_module e) in
      begin try return (FStarC.ToSyntax.ToSyntax.desugar_term dsenv t) with
          | FStarC.Errors.Error (_, e, _, _) ->
            fail ("string_to_term: " ^ Errors.rendermsg e)
          | _ -> fail ("string_to_term: Unknown error")
      end
    | ASTFragment _ -> fail ("string_to_term: expected a Term as a result, got an ASTFragment")
    | ParseError (_, err, _) -> fail ("string_to_term: got error " ^ Errors.rendermsg err) // FIXME

let push_bv_dsenv (e: Env.env) (i: string): tac (env & RD.binding)
  = let ident = Ident.mk_ident (i, FStarC.Range.dummyRange) in
    let dsenv, bv = FStarC.Syntax.DsEnv.push_bv e.dsenv ident in
    return ({ e with dsenv }, bv_to_binding bv)

let term_to_string (t:term) : tac string
  = let! g = top_env () in
    let s = Print.term_to_string' g.dsenv t in
    return s

let comp_to_string (c:comp) : tac string
  = let! g = top_env () in
    let s = Print.comp_to_string' g.dsenv c in
    return s

let term_to_doc (t:term) : tac Pprint.document
  = let! g = top_env () in
    let s = Print.term_to_doc' g.dsenv t in
    return s

let comp_to_doc (c:comp) : tac Pprint.document
  = let! g = top_env () in
    let s = Print.comp_to_doc' g.dsenv c in
    return s

let range_to_string (r:FStarC.Range.t) : tac string
  = return (show r)

let with_compat_pre_core (n:int) (f:tac 'a) : tac 'a =
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
  return vcfg

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

let free_uvars (tm : term) : tac (list int)
  = return ();!
    let uvs = Free.uvars_uncached tm
               |> elems // GGG bad, order dependent, but userspace does not have sets
               |> List.map (fun u -> UF.uvar_id u.ctx_uvar_head)
    in
    return uvs

let all_ext_options () : tac (list (string & string))
  = return () ;!
    return (Options.Ext.all ())

let ext_getv (k:string) : tac string
  = return () ;!
    return (Options.Ext.get k)

let ext_enabled (k:string) : tac bool
  = return () ;!
    return (Options.Ext.enabled k)

let ext_getns (ns:string) : tac (list (string & string))
  = return () ;!
    return (Options.Ext.getns ns)

let alloc (x:'a) : tac (tref 'a) =
  return ();!
  return (mk_ref x)

let read (r:tref 'a) : tac 'a =
  return ();!
  return (!r)

let write (r:tref 'a) (x:'a) : tac unit =
  return ();!
  r := x;
  return ()

let splice_quals () : tac (list RD.qualifier) =
  let! ps = get in
  let quals = ps.splice_quals in
  let quals = quals |> List.map syntax_to_rd_qual in
  return quals

let splice_attrs () : tac (list attribute) =
  let! ps = get in
  return ps.splice_attrs

(***** Builtins used in the meta DSL framework *****)

(* reflection typing calls generate guards in this format, and are mostly discharged
   internally. *)
type refl_guard_and_tok_t = env & Core.guard_and_tok_t

let dbg_refl (g:env) (msg:unit -> string) =
  if !dbg_ReflTc
  then Format.print_string (msg ())

let uvar_solution = bv & term
let remaining_uvar_t = bv & typ
let remaining_uvars_t = list remaining_uvar_t
let issues = list FStarC.Errors.issue
let refl_tac (a : Type) = tac (option a & issues)

let refl_typing_guard (e:env) (g:Core.guard_and_tok_t) : tac unit =
  let reason = "refl_typing_guard" in
  let g, tok = g in
  proc_guard_formula "refl_typing_guard" e g (Some tok) None (Env.get_range e)

let uncurry f (x, y) = f x y

let exn_to_issue (e:exn) : Errors.issue =
  FStarC.Errors.({
    issue_msg = Errors.mkmsg (Util.print_exn e);
    issue_level = EError;
    issue_range = None;
    issue_number = (Some 17);
    issue_ctx = get_ctx ()
  })

let __refl_typing_builtin_wrapper (f:unit -> 'a & list refl_guard_and_tok_t) : tac (option 'a & issues) =
  (* We ALWAYS rollback the state. This wrapper is meant to ensure that
  the UF graph is not affected by whatever we are wrapping. This means
  any returned term must be deeply-compressed. The guards are compressed by
  this wrapper, and handled according to the guard policy, so no action is needed
  in the wrapped function `f`. *)
  let tx = UF.new_transaction () in
  let errs, r =
    try Errors.catch_errors_and_ignore_rest f
    with exn -> //catch everything
      let issue = exn_to_issue exn in
      [issue], None
  in

  (* Deep compress the guards since we are about to roll back the UF.
  The caller will discharge them if needed. *)
  let gs : list (env & (S.term & Core.guard_commit_token_cb)) =
    if Some? r then
      let allow_uvars = false in
      let allow_names = true in (* terms are potentially open, names are OK *)
      List.map (fun (e,(g, tok)) -> e, (SC.deep_compress allow_uvars allow_names g, tok)) (snd (Some?.v r))
    else
      []
  in
  (* If r is Some, extract the result, that's what we return *)
  let r = Option.map fst r in

  (* Compress the id info table. *)
  let! ps = get in
  Env.promote_id_info ps.main_context (FStarC.TypeChecker.Tc.compress_and_norm ps.main_context);

  UF.rollback tx;

  (* Make sure to return None if any error was logged. *)
  if List.length errs > 0
  then return (None, errs)
  else (
    (* Try to discharge the guards, but if any of them fails, return a decent error. *)
    let! ok, guard_errs =
      fold_right (fun (e,g) (ok, errs) ->
        match! catch (refl_typing_guard e g) with
        | Inr () -> return (ok, errs)
        | Inl e ->
          let issue_msg = [
              Pprint.doc_of_string "Discharging guard failed.";
              Pprint.doc_of_string "g = " ^^ pp (fst g);
              Pprint.doc_of_string "Guard policy is" ^/^ pp ps.guard_policy;
            ] in
          let issue_number = Some 17 in
          let iss =
            let open FStarC.Errors in
            match issue_of_exn e with
            | Some iss -> { iss with issue_msg = issue_msg @ iss.issue_msg; issue_number }
            | None -> match e with
              | TacticFailure (msg, issue_range) ->
                { issue_msg = issue_msg @ msg; issue_level = EError; issue_range; issue_number; issue_ctx = get_ctx () }
              | _ ->
                { issue_msg = issue_msg @ [Pprint.arbitrary_string (BU.message_of_exn e)];
                  issue_level = EError; issue_range = None; issue_number; issue_ctx = get_ctx () } in
          return (false, iss :: errs)
      ) gs (true, [])
    in
    if ok then
      return (r, errs @ guard_errs)
    else
      return (None, errs @ guard_errs)
  )

(* This runs the tactic `f` in the current proofstate, and returns an
Inl if any error was raised or logged by the execution. Returns Inr with
the result otherwise. It only advances the proofstate on a success. *)
let catch_all (f : tac 'a) : tac (either issues 'a) =
  mk_tac (fun ps ->
    match Errors.catch_errors_and_ignore_rest (fun () -> Tactics.Monad.run f ps) with
    | [], Some (Success (v, ps')) -> Success (Inr v, ps')
    | errs, _ -> Success (Inl errs, ps))

(* A *second* wrapper for typing builtin primitives. The wrapper
above (__refl_typing_builtin_wrapper) is meant to catch errors in the
execution of the primitive we are calling. This second is meant to catch
errors in the tactic execution, e.g. those related to discharging the
guards if a synchronous mode (SMTSync/Force) was used.

This also adds the label to the messages (when debugging) to identify the primitive. *)
let refl_typing_builtin_wrapper (label:string) (f:unit -> 'a & list refl_guard_and_tok_t) : tac (option 'a & issues) =
  let open FStarC.Errors in
  let! o, errs =
    match! catch_all (__refl_typing_builtin_wrapper f) with
    | Inl errs -> return (None, errs)
    | Inr r -> return r
  in
  let errs =
    if Debug.any ()
    then errs |> List.map (fun is -> { is with issue_msg = is.issue_msg @ [text ("Raised within Tactics." ^ label)] })
    else errs
  in
  return (o, errs)

let no_uvars_in_term (t:term) : bool =
  t |> Free.uvars |> is_empty &&
  t |> Free.univs |> is_empty

let no_univ_uvars_in_term (t:term) : bool =
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
    issue_msg = Errors.mkmsg "Cannot check relation with uvars.";
    issue_number = Some (errno Error_UnexpectedUnresolvedUvar);
    issue_ctx = []
  } in
  i

let refl_is_non_informative (g:env) (t:typ) : tac (option unit & issues) =
  if no_uvars_in_g g &&
     no_uvars_in_term t
  then refl_typing_builtin_wrapper "refl_is_non_informative" (fun _ ->
         let g = Env.set_range g t.pos in
         dbg_refl g (fun _ ->
           Format.fmt1 "refl_is_non_informative: %s\n"
             (show t));
         let b = Core.is_non_informative g t in
         dbg_refl g (fun _ -> Format.fmt1 "refl_is_non_informative: returned %s"
                                (show b));
         if b then ((), [])
         else Errors.raise_error g Errors.Fatal_UnexpectedTerm
                "is_non_informative returned false"
  ) else (
    return (None, [unexpected_uvars_issue (Env.get_range g)])
  )

let refl_check_relation (rel:relation) (smt_ok:bool) (unfolding_ok:bool) (g:env) (t0 t1:typ)
  : tac (option unit & issues) =

  if no_uvars_in_g g &&
     no_uvars_in_term t0 &&
     no_uvars_in_term t1
  then refl_typing_builtin_wrapper "refl_check_relation" (fun _ ->
         let g = Env.set_range g t0.pos in
         dbg_refl g (fun _ ->
           Format.fmt3 "refl_check_relation: %s %s %s\n"
             (show t0)
             (if rel = Subtyping then "<:?" else "=?=")
             (show t1));
         let f =
           if rel = Subtyping
           then Core.check_term_subtyping
           else Core.check_term_equality in
         match f smt_ok unfolding_ok g t0 t1 with
         | Inl None ->
           dbg_refl g (fun _ -> "refl_check_relation: succeeded (no guard)\n");
           ((), [])
         | Inl (Some guard_f) ->
           dbg_refl g (fun _ -> "refl_check_relation: succeeded\n");
           ((), [(g, guard_f)])
         | Inr err ->
           dbg_refl g (fun _ -> Format.fmt1 "refl_check_relation failed: %s\n" (Core.print_error err));
           Errors.raise_error g Errors.Fatal_IllTyped
             ("check_relation failed: " ^ (Core.print_error err)))
  else (
    return (None, [unexpected_uvars_issue (Env.get_range g)])
  )

let refl_check_subtyping (g:env) (t0 t1:typ) : tac (option unit & issues) =
  refl_check_relation Subtyping true true g t0 t1

let t_refl_check_equiv = refl_check_relation Equality

let to_must_tot (eff:Core.tot_or_ghost) : bool =
  match eff with
  | Core.E_Total -> true
  | Core.E_Ghost -> false

let tot_or_ghost_to_string = function
  | Core.E_Total -> "E_Total"
  | Core.E_Ghost -> "E_Ghost"

let refl_norm_type (g:env) (t:typ) : typ =
  N.normalize [Env.Beta; Env.Exclude Zeta] g t

let refl_core_compute_term_type (g:env) (e:term) : tac (option (Core.tot_or_ghost & typ) & issues) =
  if no_uvars_in_g g &&
     no_uvars_in_term e
  then refl_typing_builtin_wrapper "refl_core_compute_term_type" (fun _ ->
         let g = Env.set_range g e.pos in
         dbg_refl g (fun _ ->
           Format.fmt1 "refl_core_compute_term_type: %s\n" (show e));
         match Core.compute_term_type g e with
         | Inl (eff, t, guard) ->
           let t = refl_norm_type g t in
           dbg_refl g (fun _ ->
             Format.fmt2 "refl_core_compute_term_type for %s computed type %s\n"
               (show e)
               (show t));
            let guards =
              match guard with
              | None -> []
              | Some guard -> [g, guard]
            in
           ((eff, t), guards)
         | Inr err ->
           dbg_refl g (fun _ -> Format.fmt1 "refl_core_compute_term_type: %s\n" (Core.print_error err));
           Errors.raise_error g Errors.Fatal_IllTyped 
             ("core_compute_term_type failed: " ^ (Core.print_error err)))
  else return (None, [unexpected_uvars_issue (Env.get_range g)])

let refl_core_check_term (g:env) (e:term) (t:typ) (eff:Core.tot_or_ghost)
  : tac (option unit & issues) =

  if no_uvars_in_g g &&
     no_uvars_in_term e &&
     no_uvars_in_term t
  then refl_typing_builtin_wrapper "refl_core_check_term" (fun _ ->
         let g = Env.set_range g e.pos in
         dbg_refl g (fun _ ->
           Format.fmt3 "refl_core_check_term: term: %s, type: %s, eff: %s\n"
             (show e) (show t) (show eff));
         let must_tot = to_must_tot eff in
         match Core.check_term g e t must_tot with
         | Inl None ->
           dbg_refl g (fun _ -> "refl_core_check_term: succeeded with no guard\n");
           ((), [])
         | Inl (Some guard) ->
           dbg_refl g (fun _ -> "refl_core_check_term: succeeded with guard\n");
           ((), [(g, guard)])
         | Inr err ->
           dbg_refl g (fun _ -> Format.fmt1 "refl_core_check_term failed: %s\n" (Core.print_error err));
           Errors.raise_error g Errors.Fatal_IllTyped 
             ("refl_core_check_term failed: " ^ (Core.print_error err)))
  else return (None, [unexpected_uvars_issue (Env.get_range g)])

let refl_core_check_term_at_type (g:env) (e:term) (t:typ)
  : tac (option Core.tot_or_ghost & issues) =

  if no_uvars_in_g g &&
     no_uvars_in_term e &&
     no_uvars_in_term t
  then refl_typing_builtin_wrapper "refl_core_check_term_at_type" (fun _ ->
         let g = Env.set_range g e.pos in
         dbg_refl g (fun _ ->
           Format.fmt2 "refl_core_check_term_at_type: term: %s, type: %s\n"
             (show e) (show t));
         match Core.check_term_at_type g e t with
         | Inl (eff, None) ->
           dbg_refl g (fun _ ->
             Format.fmt1 "refl_core_check_term_at_type: succeeded with eff %s and no guard\n"
               (tot_or_ghost_to_string eff));
           (eff, [])
         | Inl (eff, Some guard) ->
           dbg_refl g (fun _ ->
             Format.fmt1 "refl_core_check_term_at_type: succeeded with eff %s and guard\n"
               (tot_or_ghost_to_string eff));
           (eff, [(g, guard)])
         | Inr err ->
           dbg_refl g (fun _ -> Format.fmt1 "refl_core_check_term_at_type failed: %s\n" (Core.print_error err));
           Errors.raise_error g Errors.Fatal_IllTyped
             ("refl_core_check_term failed: " ^ (Core.print_error err)))
  else return (None, [unexpected_uvars_issue (Env.get_range g)])

let refl_tc_term (g:env) (e:term) : tac (option (term & (Core.tot_or_ghost & typ)) & issues) =
  if no_uvars_in_g g &&
     no_uvars_in_term e
  then refl_typing_builtin_wrapper "refl_tc_term" (fun _ ->
    let g = Env.set_range g e.pos in
    dbg_refl g (fun _ ->
      Format.fmt2 "refl_tc_term@%s: %s\n" (show e.pos) (show e));
    dbg_refl g (fun _ -> "refl_tc_term: starting tc {\n");
    //
    // we don't instantiate implicits at the end of e
    // it is unlikely that we will be able to resolve them,
    //   and refl typechecking API will fail if there are unresolved uvars
    //
    // note that this will still try to resolve implicits within e
    // the typechecker does not check for this env flag for such implicits
    //
    let g = {g with instantiate_imp=false} in
    //
    // lax check to elaborate
    //
    let e =
      let g = {g with phase1 = true; admit = true} in
      //
      // AR: we are lax checking to infer implicits,
      //     ghost is ok
      //
      let must_tot = false in
      let e, _, guard = g.typeof_tot_or_gtot_term g e must_tot in
      Rel.force_trivial_guard g guard;
      e in
    try
     begin
     if not (no_uvars_in_term e)
     then (
        Errors.raise_error e Errors.Error_UnexpectedUnresolvedUvar
          (Format.fmt1 "Elaborated term has unresolved implicits: %s" (show e))
     )
     else ( 
      let allow_uvars = false in
      let allow_names = true in (* terms are potentially open, names are OK *)
      let e = SC.deep_compress allow_uvars allow_names e in
      // TODO: may be should we check here that e has no unresolved implicits?
      dbg_refl g (fun _ ->
        Format.fmt1 "} finished tc with e = %s\n"
          (show e));
      match Core.compute_term_type g e with
      | Inl (eff, t, guard) ->
          let t = refl_norm_type g t in
          dbg_refl g (fun _ ->
            Format.fmt3 "refl_tc_term@%s for %s computed type %s\n"
              (show e.pos)
              (show e)
              (show t));
          let guards =
            match guard with
            | None -> []
            | Some guard -> [g, guard]
          in
          ((e, (eff, t)), guards)
      | Inr err ->
        dbg_refl g (fun _ -> Format.fmt1 "refl_tc_term failed: %s\n" (Core.print_error err));
        Errors.raise_error e Errors.Fatal_IllTyped ("tc_term callback failed: " ^ Core.print_error err)
     )
    end
    with
    | Errors.Error (Errors.Error_UnexpectedUnresolvedUvar, _, _, _) ->
      Errors.raise_error e Errors.Fatal_IllTyped "UVars remaing in term after tc_term callback")
  else
    return (None, [unexpected_uvars_issue (Env.get_range g)])

let refl_universe_of (g:env) (e:term) : tac (option universe & issues) =
  let check_univ_var_resolved g u =
    match SS.compress_univ u with
    | S.U_unif _ -> Errors.raise_error g Errors.Fatal_IllTyped "Unresolved variable in universe_of callback"
    | u -> u in

  if no_uvars_in_g g &&
     no_uvars_in_term e
  then refl_typing_builtin_wrapper "refl_universe_of" (fun _ ->
         let g = Env.set_range g e.pos in
         let t, u = U.type_u () in
         let must_tot = false in
         match Core.check_term g e t must_tot with
         | Inl None -> (check_univ_var_resolved g u, [])
         | Inl (Some guard) ->
           (check_univ_var_resolved g u, [(g, guard)])
         | Inr err ->
           dbg_refl g (fun _ -> Format.fmt1 "refl_universe_of failed: %s\n" (Core.print_error err));
           Errors.raise_error g Errors.Fatal_IllTyped ("universe_of failed: " ^ Core.print_error err))
  else return (None, [unexpected_uvars_issue (Env.get_range g)])

let refl_check_prop_validity (g:env) (e:term) : tac (option unit & issues) =
  if no_uvars_in_g g &&
     no_uvars_in_term e
  then refl_typing_builtin_wrapper "refl_check_prop_validity" (fun _ ->
         let g = Env.set_range g e.pos in
         ((), [(g, (e, Core.empty_token))])
       )
  else return (None, [unexpected_uvars_issue (Env.get_range g)])

let refl_check_match_complete (g:env) (sc:term) (scty:typ) (pats : list RD.pattern)
: tac (option (list RD.pattern & list (list RD.binding)) & issues)
=
  refl_typing_builtin_wrapper "refl_check_match_complete" fun _ ->
  (* We just craft a match with the sc and patterns, using `1` in every
  branch, and check it against type int. *)
  let one = U.exp_int "1" in
  let brs = List.map (fun p -> let p = pack_pat p in (p, None, one)) pats in
  let mm = mk (Tm_match {scrutinee=sc; ret_opt=None; brs=brs; rc_opt=None}) sc.pos in
  let env = g in
  let env = Env.set_expected_typ env S.t_int in
  let mm, _, guard = TcTerm.typeof_tot_or_gtot_term env mm true in

  Rel.force_trivial_guard env guard;
  let get_pats t =
    match (U.unmeta t).n with
    | Tm_match {brs} ->
      List.map (fun br -> let (p,_,_) = SS.open_branch br in p) brs
      (* ^We must open the patterns to return proper binders. See Pulse isse #357. *)
    | _ -> failwith "refl_check_match_complete: not a match?"
  in
  let mm = SC.deep_compress false true mm in // important! we must return fully-compressed patterns
  let pats = get_pats mm in
  let rec bnds_for_pat (p:pat) : list RD.binding =
    match p.v with
    | Pat_constant _ -> []
    | Pat_cons (fv, _, pats) -> List.concatMap (fun (p, _) -> bnds_for_pat p) pats
    | Pat_var bv -> [bv_to_binding bv]
    | Pat_dot_term _ -> []
  in
  (List.map inspect_pat pats, List.map bnds_for_pat pats), []

let refl_instantiate_implicits (g:env) (e:term) (expected_typ : option term)
  (inst_extra:bool)
  : tac (option (list (bv & typ) & term & typ) & issues) =
  if no_uvars_in_g g &&
     no_uvars_in_term e
  then refl_typing_builtin_wrapper "refl_instantiate_implicits" (fun _ ->
    let g = Env.set_range g e.pos in
    dbg_refl g (fun _ ->
      Format.fmt1 "refl_instantiate_implicits: %s\n" (show e));
    dbg_refl g (fun _ -> "refl_instantiate_implicits: starting tc {\n");
    // AR: ghost is ok for instantiating implicits
    let must_tot = false in
    let g =
      match expected_typ with
      | None -> Env.clear_expected_typ g |> fst
      | Some typ -> Env.set_expected_typ g typ
    in
    let g = {g with instantiate_imp=inst_extra; phase1=true; admit=true} in
    let e, t, guard = g.typeof_tot_or_gtot_term g e must_tot in
    //
    // We don't worry about the logical payload,
    //   since this API does not return proof of typing
    //
    let guard = guard |> Rel.solve_deferred_constraints g |> Rel.resolve_implicits g in
    let bvs_and_ts : list (bv & typ) =
      match Listlike.to_list guard.implicits with
      | [] -> []
      | imps ->
        //
        // We could not solve all implicits
        //
        // Create fresh names for the unsolved uvars, and
        //   set the solution for the uvars to these names
        // This way when we compress the terms later,
        //   the uvars will be substituted with the names
        //
        let l : list (uvar & typ & bv) =
          imps
          |> List.map (fun {imp_uvar} ->
                       (imp_uvar.ctx_uvar_head,
                        U.ctx_uvar_typ imp_uvar,
                        S.new_bv None (S.mk Tm_unknown Range.dummyRange)))
        in
        l |> List.iter (fun (uv, _, bv) -> U.set_uvar uv (S.bv_to_name bv));
        List.map (fun (_, t, bv) -> bv, t) l
    in

    dbg_refl g (fun _ -> Format.fmt2 "refl_instantiate_implicits: inferred %s : %s" (show e) (show t));

    // Stop now if we've already logged errors, it's less confusing to the user.
    Errors.stop_if_err ();

    if not (no_univ_uvars_in_term e)
    then Errors.raise_error e Errors.Error_UnexpectedUnresolvedUvar
           (Format.fmt1 "Elaborated term has unresolved univ uvars: %s" (show e));
    if not (no_univ_uvars_in_term t)
    then Errors.raise_error e Errors.Error_UnexpectedUnresolvedUvar
           (Format.fmt1 "Inferred type has unresolved univ uvars: %s" (show t));
    bvs_and_ts |> List.iter (fun (x, t) ->
      if not (no_univ_uvars_in_term t)
      then Errors.raise_error e Errors.Error_UnexpectedUnresolvedUvar
             (Format.fmt2 "Inferred type has unresolved univ uvars:  %s:%s" (show x) (show t)));
    let g = Env.push_bvs g (List.map (fun (bv, t) -> {bv with sort=t}) bvs_and_ts) in
    let allow_uvars = false in
    let allow_names = true in (* terms are potentially open, names are OK *)
    let e = SC.deep_compress allow_uvars allow_names e in
    let t = t |> refl_norm_type g |> SC.deep_compress allow_uvars allow_names in
    let bvs_and_ts =
      bvs_and_ts |> List.map (fun (bv, t) -> bv, SC.deep_compress allow_uvars allow_names t) in

    dbg_refl g (fun _ ->
      Format.fmt2 "} finished tc with e = %s and t = %s\n"
        (show e)
        (show t));
    ((bvs_and_ts, e, t), [])
  )
  else return (None, [unexpected_uvars_issue (Env.get_range g)])

let refl_try_unify (g:env) (uvs:list (bv & typ)) (t0 t1:term)
  : tac (option (list (bv & term)) & issues) =

  if no_uvars_in_g g &&
     no_uvars_in_term t0 &&
     no_uvars_in_term t1 &&
     List.for_all no_uvars_in_term (List.map snd uvs)
  then refl_typing_builtin_wrapper "refl_try_unify" (fun _ ->
    dbg_refl g (fun _ -> Format.fmt3 "refl_try_unify %s and %s, with uvs: %s {\n"
                           (show t0)
                           (show t1)
                           (show uvs));
    let g = Env.set_range g t0.pos in
    //
    // create uvars for the bvs in uvs,
    //   and maintain a mapping from uvars to bvs in tbl
    // we apply substitutions to uvs accordingly (replacing uvs names with newly created uvars)
    //
    let guard_uvs, ss, tbl = List.fold_left (fun (guard_uvs, ss, tbl) (bv, t) ->
      let t = SS.subst ss t in
      let uv_t, (ctx_u, _), guard_uv =
        // the API doesn't promise well-typedness of the solutions
        let reason = Format.fmt1 "refl_try_unify for %s" (show bv) in
        let should_check_uvar = Allow_untyped "refl_try_unify" in
        Env.new_implicit_var_aux reason t0.pos g t should_check_uvar None false
      in
      let uv_id = Syntax.Unionfind.uvar_unique_id ctx_u.ctx_uvar_head in
      Env.conj_guard guard_uvs guard_uv,
      (NT (bv, uv_t))::ss,
      PIMap.add tbl uv_id (ctx_u.ctx_uvar_head, bv)
    ) (Env.trivial_guard, [], (PIMap.empty ())) uvs in
    let t0, t1 = SS.subst ss t0, SS.subst ss t1 in
    let g = { g with phase1=true; admit=true } in
    let guard_eq =
      let smt_ok = true in
      Rel.try_teq smt_ok g t0 t1 in
    let l =
      match guard_eq with
      | None -> []  // could not unify
      | Some guard ->
        let guard = Env.conj_guard guard_uvs guard in
        let guard = guard |> Rel.solve_deferred_constraints g |> Rel.resolve_implicits g in

        //
        // if there is some unresolved implicit that was not part of uvs,
        //   e.g., created as part of Rel.try_teq, return []
        //
        let b = List.existsb (fun {imp_uvar = {ctx_uvar_head = (uv, _, _)}} ->
          PIMap.try_find tbl (Unionfind.puf_unique_id uv) = None) (Listlike.to_list guard.implicits) in
        if b then []
        else
          //
          // iterate over the tbl
          // return uvs that could be solved fully
          //
          PIMap.fold tbl (fun id (uvar, bv) l ->
            match Syntax.Unionfind.find uvar with
            | Some t ->
              let allow_uvars = true in
              let allow_names = true in
              let t = SC.deep_compress allow_uvars allow_names t in
              if t |> Syntax.Free.uvars_full |> is_empty
              then (bv, t)::l
              else l
            | None -> l
          ) [] in
    dbg_refl g (fun _ -> Format.fmt1 "} refl_try_unify, substitution is: %s\n" (show l));
    l, [] 
  )
  else return (None, [unexpected_uvars_issue (Env.get_range g)])


let refl_maybe_relate_after_unfolding (g:env) (t0 t1:typ)
  : tac (option Core.side & issues) =

  if no_uvars_in_g g &&
     no_uvars_in_term t0 &&
     no_uvars_in_term t1
  then refl_typing_builtin_wrapper "refl_maybe_relate_after_unfolding" (fun _ ->
        let g = Env.set_range g t0.pos in
         dbg_refl g (fun _ ->
           Format.fmt2 "refl_maybe_relate_after_unfolding: %s and %s {\n"
             (show t0)
             (show t1));
         let s = Core.maybe_relate_after_unfolding g t0 t1 in
         dbg_refl g (fun _ ->
           Format.fmt1 "} returning side: %s\n" (show s));
         s, [])
  else return (None, [unexpected_uvars_issue (Env.get_range g)])

let refl_maybe_unfold_head (g:env) (e:term) : tac (option term & issues) =
  if no_uvars_in_g g &&
     no_uvars_in_term e
  then refl_typing_builtin_wrapper "refl_maybe_unfold_head" (fun _ ->
    let g = Env.set_range g e.pos in
    dbg_refl g (fun _ ->
      Format.fmt1 "refl_maybe_unfold_head: %s {\n" (show e));
    let eopt = N.maybe_unfold_head g e in
    dbg_refl g (fun _ ->
      Format.fmt1 "} eopt = %s\n"
        (match eopt with
         | None -> "none"
         | Some e -> show e));
    if eopt = None
    then Errors.raise_error e Errors.Fatal_UnexpectedTerm
           (Format.fmt1 "Could not unfold head: %s\n" (show e))
    else (eopt |> Some?.v, []))
  else return (None, [unexpected_uvars_issue (Env.get_range g)])

let push_open_namespace (e:env) (ns:list string) =
  let lid = Ident.lid_of_path ns Range.dummyRange in
  return { e with dsenv = FStarC.Syntax.DsEnv.push_namespace e.dsenv lid Unrestricted }

let push_module_abbrev (e:env) (n:string) (m:list string) =
  let mlid = Ident.lid_of_path m Range.dummyRange in
  let ident = Ident.id_of_text n in
  return { e with dsenv = FStarC.Syntax.DsEnv.push_module_abbrev e.dsenv ident mlid }

let resolve_name (e:env) (n:list string) =
  let l = Ident.lid_of_path n Range.dummyRange in
  return (FStarC.Syntax.DsEnv.resolve_name e.dsenv l)

let log_issues (is : list Errors.issue) : tac unit =
  let open FStarC.Errors in
  let! ps = get in
  (* Prepend an error component, unless the tactic handles its own errors. *)
  let is =
    if ps.dump_on_failure
    then
      is |>
      List.map (fun i -> { i with issue_msg = (Errors.text "Tactic logged issue:")::i.issue_msg })
    else
      is
  in
  add_issues is;
  return ()

(**** Creating proper environments and proofstates ****)

let tac_env (env:Env.env) : Env.env =
    let env, _ = Env.clear_expected_typ env in
    let env = { env with Env.instantiate_imp = false } in
    let env = { env with failhard = true } in
    let env = { env with enable_defer_to_tac = false } in
    env

let proofstate_of_goals rng env goals imps =
    let env = tac_env env in
    let ps = {
        main_context = env;
        all_implicits = imps;
        goals = goals;
        smt_goals = [];

        splice_quals = [];
        splice_attrs = [];

        depth = 0;
        __dump = do_dump_proofstate;
        psc = PO.null_psc;
        entry_range = rng;
        guard_policy = SMT;
        freshness = 0;
        tac_verb_dbg = !dbg_TacVerbose;
        local_state = PSMap.empty ();
        urgency = 1;
        dump_on_failure = true;
    }
    in
    ps

let proofstate_of_goal_ty rng env typ =
    let env = { env with range = rng } in
    let env = tac_env env in
    let g, g_u = goal_of_goal_ty env typ in
    let ps = proofstate_of_goals rng env [g] (Listlike.to_list g_u.implicits) in
    (ps, goal_witness g)

let proofstate_of_all_implicits rng env imps =
    let env = tac_env env in
    let goals = List.map (goal_of_implicit env) imps in
    let w = goal_witness (List.hd goals) in
    let ps = {
        main_context = env;
        all_implicits = imps;
        goals = goals;
        smt_goals = [];
        splice_quals = [];
        splice_attrs = [];
        depth = 0;
        __dump = do_dump_proofstate;
        psc = PO.null_psc;
        entry_range = rng;
        guard_policy = SMT;
        freshness = 0;
        tac_verb_dbg = !dbg_TacVerbose;
        local_state = PSMap.empty ();
        urgency = 1;
        dump_on_failure = true;
    }
    in
    (ps, w)

let getprop (e:Env.env) (t:term) : option term =
    let tn = N.normalize [Env.Weak; Env.HNF; Env.UnfoldUntil delta_constant] e t in
    U.un_squash tn

let run_unembedded_tactic_on_ps_and_solve_remaining
    (t_range g_range : Range.t)
    (background : bool)
    (t : 'a)
    (f : 'a -> tac 'b)
    (ps : proofstate)
    : 'b
=
  let remaining_goals, r = FStarC.Tactics.Interpreter.run_unembedded_tactic_on_ps t_range g_range background t f ps in
  // Check that all goals left are irrelevant and provable
  remaining_goals |> List.iter (fun g ->
      match getprop (goal_env g) (goal_type g) with
      | Some vc ->
          let guard = guard_of_guard_formula (NonTrivial vc) in
          Rel.force_trivial_guard (goal_env g) guard
      | None ->
          Err.raise_error g_range Err.Fatal_OpenGoalsInSynthesis "tactic left a computationally-relevant goal unsolved");
  r

let call_subtac (g:env) (f : tac unit) (_u:universe) (goal_ty : typ) : tac (option term & issues) =
  return ();! // thunk
  let rng = Env.get_range g in
  let ps, w = proofstate_of_goal_ty rng g goal_ty in
  let ps = { ps with dump_on_failure = false } in // subtacs can fail gracefully, do not dump the failed proofstate.
  match Errors.catch_errors_and_ignore_rest (fun () ->
          run_unembedded_tactic_on_ps_and_solve_remaining rng rng false () (fun () -> f) ps)
  with
  | [], Some () ->
    return (Some w, [])
  | issues, _ ->
    return (None, issues)

let run_tactic_on_ps_and_solve_remaining
    (#a #b : Type)
    (t_range g_range : Range.t)
    (background : bool)
    (t : a)
    (f_tm : term)
    (ps : proofstate)
    : unit
=
  let remaining_goals, r = FStarC.Tactics.Interpreter.run_tactic_on_ps #unit #unit t_range g_range background TC.solve () TC.solve f_tm false ps in
  // Check that all goals left are irrelevant and provable
  remaining_goals |> List.iter (fun g ->
      match getprop (goal_env g) (goal_type g) with
      | Some vc ->
          let guard = guard_of_guard_formula (NonTrivial vc) in
          Rel.force_trivial_guard (goal_env g) guard
      | None ->
          Err.raise_error g_range Err.Fatal_OpenGoalsInSynthesis "tactic left a computationally-relevant goal unsolved");
  r

let call_subtac_tm (g:env) (f_tm : term) (_u:universe) (goal_ty : typ) : tac (option term & issues) =
  return ();! // thunk
  let rng = Env.get_range g in
  let ps, w = proofstate_of_goal_ty rng g goal_ty in
  let ps = { ps with dump_on_failure = false } in // subtacs can fail gracefully, do not dump the failed proofstate.
  match Errors.catch_errors_and_ignore_rest (fun () ->
          run_tactic_on_ps_and_solve_remaining #unit #unit rng rng false () f_tm ps)
  with
  | [], Some () ->
    return (Some w, [])
  | issues, _ ->
    return (None, issues)

let stats_record (a:'a) (wp:'b) (s:string) (f : tac 'c) : tac 'c =
  mk_tac (fun ps ->
    Stats.record s (fun () -> run f ps))

let with_error_context (a:'a) (wp:'b) (s:string) (f : tac 'c) : tac 'c =
  mk_tac (fun ps ->
    Errors.with_ctx s (fun () -> run f ps))

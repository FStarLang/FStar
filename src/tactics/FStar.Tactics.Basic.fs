#light "off"
module FStar.Tactics.Basic

open FStar
open FStar.Pervasives
open FStar.All
open FStar.Syntax.Syntax
open FStar.Util
open FStar.Ident
open FStar.TypeChecker.Env
open FStar.TypeChecker.Common
open FStar.Reflection.Data
open FStar.Reflection.Basic
open FStar.Tactics.Result
open FStar.Tactics.Types
open FStar.Tactics.Monad
open FStar.Tactics.Printing

module BU     = FStar.Util
module Cfg    = FStar.TypeChecker.Cfg
module EMB    = FStar.Syntax.Embeddings
module Env    = FStar.TypeChecker.Env
module Err    = FStar.Errors
module N      = FStar.TypeChecker.Normalize
module PC     = FStar.Parser.Const
module Print  = FStar.Syntax.Print
module Rel    = FStar.TypeChecker.Rel
module SF     = FStar.Syntax.Free
module S      = FStar.Syntax.Syntax
module SS     = FStar.Syntax.Subst
module TcComm = FStar.TypeChecker.Common
module TcTerm = FStar.TypeChecker.TcTerm
module TcUtil = FStar.TypeChecker.Util
module UF     = FStar.Syntax.Unionfind
module U      = FStar.Syntax.Util
module Z      = FStar.BigInt

type name = bv
type env = Env.env
type implicits = Env.implicits

let rangeof g = g.goal_ctx_uvar.ctx_uvar_range

// Beta reduce
let normalize s e t = N.normalize_with_primitive_steps FStar.Reflection.Interpreter.reflection_primops s e t
let bnorm e t = normalize [] e t
let whnf e t = N.unfold_whnf e t

(* Use this one for everything the user is supposed to see, EXCEPT
 * STATE DUMPS, as it does resugaring. For debug messages, just use plain
 * term_to_string, we don't want to cause normalization with debug
 * flags. *)
let tts = N.term_to_string

let term_to_string e t = Print.term_to_string' e.dsenv t

let bnorm_goal g = goal_with_type g (bnorm (goal_env g) (goal_type g))

let tacprint  (s:string)       = BU.print1 "TAC>> %s\n" s
let tacprint1 (s:string) x     = BU.print1 "TAC>> %s\n" (BU.format1 s x)
let tacprint2 (s:string) x y   = BU.print1 "TAC>> %s\n" (BU.format2 s x y)
let tacprint3 (s:string) x y z = BU.print1 "TAC>> %s\n" (BU.format3 s x y z)

let print (msg:string) : tac<unit> =
    if not (Options.silent ()) then
      tacprint msg;
    ret ()

let debugging () : tac<bool> =
    bind get (fun ps ->
    ret (Env.debug ps.main_context (Options.Other "Tac")))

let do_dump_ps (msg:string) (ps:proofstate) : unit =
  let psc = ps.psc in
  let subst = Cfg.psc_subst psc in
  do_dump_proofstate (subst_proof_state subst ps) msg

let dump (msg:string) : tac<unit> =
  mk_tac (fun ps ->
    do_dump_ps msg ps;
    Success ((), ps))

let dump_all (print_resolved:bool) (msg:string) : tac<unit> =
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

let dump_uvars_of (g:goal) (msg:string) : tac<unit> =
  mk_tac (fun ps ->
    let uvs = SF.uvars (goal_type g) |> BU.set_elements in
    let gs = List.map (goal_of_ctx_uvar g) uvs in
    let gs = List.filter (fun g -> not (check_goal_solved g)) gs in
    let ps' = { ps with smt_goals = [] ; goals = gs } in
    do_dump_ps msg ps';
    Success ((), ps))

let fail1 msg x     = fail (BU.format1 msg x)
let fail2 msg x y   = fail (BU.format2 msg x y)
let fail3 msg x y z = fail (BU.format3 msg x y z)
let fail4 msg x y z w = fail (BU.format4 msg x y z w)

let destruct_eq' (typ : typ) : option<(term * term)> =
    match U.destruct_typ_as_formula typ with
    | Some (U.BaseConn(l, [_; (e1, None); (e2, None)]))
      when Ident.lid_equals l PC.eq2_lid
      ||   Ident.lid_equals l PC.c_eq2_lid
      ->
        Some (e1, e2)
    | Some (U.BaseConn(l, [_; _; (e1, _); (e2, _)]))
      when Ident.lid_equals l PC.eq3_lid
      ->
        Some (e1, e2)
    | _ ->
      match U.unb2t typ with
      | None -> None
      | Some t ->
        begin
        let hd, args = U.head_and_args t in
        match (SS.compress hd).n, args with
        | Tm_fvar fv, [(_, Some (Implicit _)); (e1, None); (e2, None)] when S.fv_eq_lid fv PC.op_Eq ->
            Some (e1, e2)
        | _ -> None
        end

let destruct_eq (typ : typ) : option<(term * term)> =
    match destruct_eq' typ with
    | Some t -> Some t
    | None ->
        // Retry for a squashed one
        begin match U.un_squash typ with
        | Some typ -> destruct_eq' typ
        | None -> None
        end

let __do_unify_wflags (dbg:bool) (allow_guards:bool)
               (env : env) (t1 : term) (t2 : term)
: tac<option<guard_t>> =
    if dbg then
      BU.print2 "%%%%%%%%do_unify %s =? %s\n" (Print.term_to_string t1)
                                              (Print.term_to_string t2);
    try
        let res =
          if allow_guards
          then Rel.try_teq true env t1 t2
          else Rel.teq_nosmt env t1 t2
        in
        if dbg then
          BU.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                              (FStar.Common.string_of_option (Rel.guard_to_string env) res)
                              (Print.term_to_string t1)
                              (Print.term_to_string t2);

        match res with
        | None ->
          ret None
        | Some g ->
          bind (add_implicits g.implicits) (fun () ->
          ret (Some g))

    with | Errors.Err (_, msg, _) -> begin
            mlog (fun () -> BU.print1 ">> do_unify error, (%s)\n" msg ) (fun _ ->
            ret None)
            end
         | Errors.Error (_, msg, r, _) -> begin
            mlog (fun () -> BU.print2 ">> do_unify error, (%s) at (%s)\n"
                                msg (Range.string_of_range r)) (fun _ ->
            ret None)
            end

(* Just a wrapper over __do_unify_wflags to better debug *)
let __do_unify (allow_guards:bool) (env : env) (t1 : term) (t2 : term)
: tac<option<guard_t>> =
    let dbg = Env.debug env (Options.Other "TacUnify") in
    bind idtac (fun () ->
    if dbg then begin
        Options.push ();
        let _ = Options.set_options "--debug_level Rel --debug_level RelCheck" in
        ()
    end;
    bind (__do_unify_wflags dbg allow_guards env t1 t2) (fun r ->
    if dbg then
        Options.pop ();
    (* bind compress_implicits (fun _ -> *)
    ret r))


(* SMT-free unification. *)
let do_unify (env : env) (t1 : term) (t2 : term)
: tac<bool> =
  bind (__do_unify false env t1 t2) (function
  | None -> ret false
  | Some g ->
    (* g has to be trivial and we have already added its implicits *)
    if not (Env.is_trivial_guard_formula g) then
      failwith "internal error: do_unify: guard is not trivial";
    ret true
  )

let do_unify' (allow_guards : bool) (env : env) (t1 : term) (t2 : term)
: tac<option<guard_t>> =
  __do_unify allow_guards env t1 t2

(* Does t1 match t2? That is, do they unify without instantiating/changing t1? *)
let do_match (env:Env.env) (t1:term) (t2:term) : tac<bool> =
    bind (mk_tac (fun ps -> let tx = UF.new_transaction () in
                            Success (tx, ps))) (fun tx ->
    let uvs1 = SF.uvars_uncached t1 in
    bind (do_unify env t1 t2) (fun r ->
    if r then begin
        let uvs2 = SF.uvars_uncached t1 in
        if not (set_eq uvs1 uvs2)
        then (UF.rollback tx; ret false)
        else ret true
    end
    else ret false
    ))

(* This is a bandaid. It's similar to do_match but checks that the
LHS of the equality in [t1] is not instantiated, but the RHS might be.
It is a pain to expose the whole logic to tactics, so we just do it
here for now. *)
let do_match_on_lhs (env:Env.env) (t1:term) (t2:term) : tac<bool> =
    bind (mk_tac (fun ps -> let tx = UF.new_transaction () in
                            Success (tx, ps))) (fun tx ->
    match destruct_eq t1 with
    | None -> fail "do_match_on_lhs: not an eq"
    | Some (lhs, _) ->
    let uvs1 = SF.uvars_uncached lhs in
    bind (do_unify env t1 t2) (fun r ->
    if r then begin
        let uvs2 = SF.uvars_uncached lhs in
        if not (set_eq uvs1 uvs2)
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
let set_solution goal solution : tac<unit> =
    match FStar.Syntax.Unionfind.find goal.goal_ctx_uvar.ctx_uvar_head with
    | Some _ ->
      fail (BU.format1 "Goal %s is already solved" (goal_to_string_verbose goal))
    | None ->
      FStar.Syntax.Unionfind.change goal.goal_ctx_uvar.ctx_uvar_head solution;
      ret ()

let trysolve (goal : goal) (solution : term) : tac<bool> =
    do_unify (goal_env goal) solution (goal_witness goal)

let solve (goal : goal) (solution : term) : tac<unit> =
    let e = goal_env goal in
    mlog (fun () -> BU.print2 "solve %s := %s\n" (Print.term_to_string (goal_witness goal))
                                                 (Print.term_to_string solution)) (fun () ->
    bind (trysolve goal solution) (fun b ->
    if b
    then bind dismiss (fun () -> remove_solved_goals)
    else fail (BU.format3 "%s does not solve %s : %s"
              (tts (goal_env goal) solution)
              (tts (goal_env goal) (goal_witness goal))
              (tts (goal_env goal) (goal_type goal)))))


let solve' (goal : goal) (solution : term) : tac<unit> =
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


let tadmit_t (t:term) : tac<unit> = wrap_err "tadmit_t" <|
    bind get (fun ps ->
    bind cur_goal (fun g ->
    // should somehow taint the state instead of just printing a warning
    Err.log_issue (goal_type g).pos
        (Errors.Warning_TacAdmit, BU.format1 "Tactics admitted goal <%s>\n\n"
                    (goal_to_string "" None ps g));
    solve' g t))

let fresh () : tac<Z.t> =
    bind get (fun ps ->
    let n = ps.freshness in
    let ps = { ps with freshness = n + 1 } in
    bind (set ps) (fun () ->
    ret (Z.of_int_fs n)))

let curms () : tac<Z.t> =
    ret (BU.now_ms () |> Z.of_int_fs)

(* Annoying duplication here *)
let __tc (e : env) (t : term) : tac<(term * typ * guard_t)> =
    bind get (fun ps ->
    mlog (fun () -> BU.print1 "Tac> __tc(%s)\n" (Print.term_to_string t)) (fun () ->
    let e = {e with uvar_subtyping=false} in
    try ret (TcTerm.typeof_tot_or_gtot_term e t true)
    with | Errors.Err (_, msg, _)
         | Errors.Error (_, msg, _, _) -> begin
           fail3 "Cannot type %s in context (%s). Error = (%s)" (tts e t)
                                                  (Env.all_binders e |> Print.binders_to_string ", ")
                                                  msg
           end))

let __tc_ghost (e : env) (t : term) : tac<(term * typ * guard_t)> =
    bind get (fun ps ->
    mlog (fun () -> BU.print1 "Tac> __tc_ghost(%s)\n" (Print.term_to_string t)) (fun () ->
    let e = {e with uvar_subtyping=false} in
    try let t, lc, g = TcTerm.tc_tot_or_gtot_term e t in
        ret (t, lc.res_typ, g)
    with | Errors.Err (_, msg ,_)
         | Errors.Error (_, msg, _ ,_) -> begin
           fail3 "Cannot type %s in context (%s). Error = (%s)" (tts e t)
                                                  (Env.all_binders e |> Print.binders_to_string ", ")
                                                  msg
           end))

let __tc_lax (e : env) (t : term) : tac<(term * lcomp * guard_t)> =
    bind get (fun ps ->
    mlog (fun () -> BU.print1 "Tac> __tc_lax(%s)\n" (Print.term_to_string t)) (fun () ->
    let e = {e with uvar_subtyping=false} in
    let e = {e with lax = true} in
    try ret (TcTerm.tc_term e t)
    with | Errors.Err (_, msg, _)
         | Errors.Error (_, msg, _, _) -> begin
           fail3 "Cannot type %s in context (%s). Error = (%s)" (tts e t)
                                                  (Env.all_binders e |> Print.binders_to_string ", ")
                                                  msg
           end))

let get_guard_policy () : tac<guard_policy> =
    bind get (fun ps -> ret ps.guard_policy)

let set_guard_policy (pol : guard_policy) : tac<unit> =
    bind get (fun ps -> set ({ ps with guard_policy = pol }))

let with_policy pol (t : tac<'a>) : tac<'a> =
    bind (get_guard_policy ()) (fun old_pol ->
    bind (set_guard_policy pol) (fun () ->
    bind t (fun r ->
    bind (set_guard_policy old_pol) (fun () ->
    ret r))))

let proc_guard (reason:string) (e : env) (g : guard_t) (rng:Range.range) : tac<unit> =
    mlog (fun () ->
        BU.print2 "Processing guard (%s:%s)\n" reason (Rel.guard_to_string e g)) (fun () ->
    bind (add_implicits g.implicits) (fun () ->
    match (Rel.simplify_guard e g).guard_f with
    | TcComm.Trivial -> ret ()
    | TcComm.NonTrivial f ->
    bind get (fun ps ->
    match ps.guard_policy with
    | Drop ->
        // should somehow taint the state instead of just printing a warning
        Err.log_issue e.range
            (Errors.Warning_TacAdmit, BU.format1 "Tactics admitted guard <%s>\n\n"
                        (Rel.guard_to_string e g));
        ret ()

    | Goal ->
        mlog (fun () -> BU.print2 "Making guard (%s:%s) into a goal\n" reason (Rel.guard_to_string e g)) (fun () ->
        bind (goal_of_guard reason e f rng) (fun g ->
        push_goals [g]))

    | SMT ->
        mlog (fun () -> BU.print2 "Sending guard (%s:%s) to SMT goal\n" reason (Rel.guard_to_string e g)) (fun () ->
        bind (goal_of_guard reason e f rng) (fun g ->
        push_smt_goals [g]))

    | Force ->
        mlog (fun () -> BU.print2 "Forcing guard (%s:%s)\n" reason (Rel.guard_to_string e g)) (fun () ->
        try if not (Env.is_trivial <| Rel.discharge_guard_no_smt e g)
            then
                mlog (fun () -> BU.print1 "guard = %s\n" (Rel.guard_to_string e g)) (fun () ->
                fail1 "Forcing the guard failed (%s)" reason)
            else ret ()
        with
        | _ -> mlog (fun () -> BU.print1 "guard = %s\n" (Rel.guard_to_string e g)) (fun () ->
               fail1 "Forcing the guard failed (%s)" reason)))))

let tcc (e : env) (t : term) : tac<comp> = wrap_err "tcc" <|
    bind (__tc_lax e t) (fun (_, lc, _) ->
    (* Why lax? What about the guard? It doesn't matter! tc is only
     * a way for metaprograms to query the typechecker, but
     * the result has no effect on the proofstate and nor is it
     * taken for a fact that the typing is correct. *)
    ret (TcComm.lcomp_comp lc |> fst)  //dropping the guard from lcomp_comp too!
    )

let tc (e : env) (t : term) : tac<typ> = wrap_err "tc" <|
    bind (tcc e t) (fun c -> ret (U.comp_result c))

let divide (n:Z.t) (l : tac<'a>) (r : tac<'b>) : tac<('a * 'b)> =
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
let focus (f:tac<'a>) : tac<'a> =
    bind (divide Z.one f idtac) (fun (a, ()) -> ret a)

(* Applies t to each of the current goals
      fails if t fails on any of the goals
      collects each result in the output list *)
let rec map (tau:tac<'a>): tac<(list<'a>)> =
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
let seq (t1:tac<unit>) (t2:tac<unit>) : tac<unit> =
    focus (
        bind t1 (fun _ ->
        bind (map t2) (fun _ -> ret ()))
    )

(*
  [intro]:

  Initial goal: G |- ?u : (t -> t')

  Now we do an `intro`:

  Next goal:  `G, x:t |- ?v : t'`

  with `?u := (fun (x:t) -> ?v @ [NM(x, 0)])`
*)
let intro () : tac<binder> = wrap_err "intro" <|
    bind cur_goal (fun goal ->
    match U.arrow_one (whnf (goal_env goal) (goal_type goal)) with
    | Some (b, c) ->
        if not (U.is_total_comp c)
        then fail "Codomain is effectful"
        else let env' = Env.push_binders (goal_env goal) [b] in
             let typ' = U.comp_result c in
             //BU.print1 "[intro]: current goal is %s" (goal_to_string goal);
             //BU.print1 "[intro]: current goal witness is %s" (Print.term_to_string (goal_witness goal));
             //BU.print1 "[intro]: with goal type %s" (Print.term_to_string (goal_type goal));
             //BU.print2 "[intro]: with binder = %s, new goal = %s"
             //         (Print.binders_to_string ", " [b])
             //         (Print.term_to_string typ');
             bind (new_uvar "intro" env' typ' (rangeof goal)) (fun (body, ctx_uvar) ->
             let sol = U.abs [b] body (Some (U.residual_comp_of_comp c)) in
             //BU.print1 "[intro]: solution is %s"
             //           (Print.term_to_string sol);
             //BU.print1 "[intro]: old goal is %s" (goal_to_string goal);
             //BU.print1 "[intro]: new goal is %s"
             //           (Print.ctx_uvar_to_string ctx_uvar);
             //ignore (FStar.Options.set_options "--debug_level Rel");
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
             bind (set_solution goal sol) (fun () ->
             let g = mk_goal env' ctx_uvar goal.opts goal.is_guard goal.label in
             bind (replace_cur (bnorm_goal g)) (fun _ ->
             ret b)))
    | None ->
        fail1 "goal is not an arrow (%s)" (tts (goal_env goal) (goal_type goal))
    )

// TODO: missing: precedes clause, and somehow disabling fixpoints only as needed
let intro_rec () : tac<(binder * binder)> =
    bind cur_goal (fun goal ->
    BU.print_string "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
    BU.print_string "WARNING (intro_rec): proceed at your own risk...\n";
    match U.arrow_one (whnf (goal_env goal) (goal_type goal)) with
    | Some (b, c) ->
        if not (U.is_total_comp c)
        then fail "Codomain is effectful"
        else let bv = gen_bv "__recf" None (goal_type goal) in
             let bs = [S.mk_binder bv; b] in // recursively bound name and argument we're introducing
             let env' = Env.push_binders (goal_env goal) bs in
             bind (new_uvar "intro_rec" env' (U.comp_result c) (rangeof goal)) (fun (u, ctx_uvar_u) ->
             let lb = U.mk_letbinding (Inl bv) [] (goal_type goal) PC.effect_Tot_lid (U.abs [b] u None) [] Range.dummyRange in
             let body = S.bv_to_name bv in
             let lbs, body = SS.close_let_rec [lb] body in
             let tm = mk (Tm_let ((true, lbs), body)) (goal_witness goal).pos in
             bind (set_solution goal tm) (fun () ->
             bind (replace_cur (bnorm_goal ({ goal with goal_ctx_uvar=ctx_uvar_u}))) (fun _ ->
             ret (S.mk_binder bv, b))))
    | None ->
        fail1 "intro_rec: goal is not an arrow (%s)" (tts (goal_env goal) (goal_type goal))
    )

let norm (s : list<EMB.norm_step>) : tac<unit> =
    bind cur_goal (fun goal ->
    mlog (fun () -> BU.print1 "norm: witness = %s\n" (Print.term_to_string (goal_witness goal))) (fun _ ->
    // Translate to actual normalizer steps
    let steps = [Env.Reify; Env.UnfoldTac]@(N.tr_norm_steps s) in
    //let w = normalize steps (goal_env goal) (goal_witness goal) in
    let t = normalize steps (goal_env goal) (goal_type goal) in
    replace_cur (goal_with_type goal t)
    ))

let norm_term_env (e : env) (s : list<EMB.norm_step>) (t : term) : tac<term> = wrap_err "norm_term" <|
    bind get (fun ps ->
    (* We need a set of options, but there might be no goals, so do this *)
    let opts = match ps.goals with
               | g::_ -> g.opts
               | _ -> FStar.Options.peek ()
    in
    mlog (fun () -> BU.print1 "norm_term_env: t = %s\n" (Print.term_to_string t)) (fun () ->
    // only for elaborating lifts and all that, we don't care if it's actually well-typed
    bind (__tc_lax e t) (fun (t, _, _) ->
    let steps = [Env.Reify; Env.UnfoldTac]@(N.tr_norm_steps s) in
    let t = normalize steps ps.main_context t in
    mlog (fun () -> BU.print1 "norm_term_env: t' = %s\n" (Print.term_to_string t)) (fun () ->
    ret t
    ))))

let refine_intro () : tac<unit> = wrap_err "refine_intro" <|
    bind cur_goal (fun g ->
    match Rel.base_and_refinement (goal_env g) (goal_type g) with
    | _, None -> fail "not a refinement"
    | t, Some (bv, phi) ->
        let g1 = goal_with_type g t in
        let bv, phi = match SS.open_term [S.mk_binder bv] phi with
                      | bvs, phi -> (List.hd bvs).binder_bv, phi
        in
        bind (mk_irrelevant_goal "refine_intro refinement" (goal_env g)
                    (SS.subst [S.NT (bv, (goal_witness g))] phi) (rangeof g) g.opts g.label) (fun g2 ->
        bind dismiss (fun _ ->
        add_goals [g1;g2])))

let __exact_now set_expected_typ (t:term) : tac<unit> =
    bind cur_goal (fun goal ->
    let env = if set_expected_typ
              then Env.set_expected_typ (goal_env goal) (goal_type goal)
              else (goal_env goal)
    in
    bind (__tc env t) (fun (t, typ, guard) ->
    mlog (fun () -> BU.print2 "__exact_now: got type %s\n__exact_now: and guard %s\n"
                                                     (Print.term_to_string typ)
                                                     (Rel.guard_to_string (goal_env goal) guard)) (fun _ ->
    bind (proc_guard "__exact typing" (goal_env goal) guard (rangeof goal)) (fun _ ->
    mlog (fun () -> BU.print2 "__exact_now: unifying %s and %s\n" (Print.term_to_string typ)
                                                                  (Print.term_to_string (goal_type goal))) (fun _ ->
    bind (do_unify (goal_env goal) typ (goal_type goal)) (fun b -> if b
    then solve goal t
    else
      let typ, goalt = TypeChecker.Err.print_discrepancy (tts (goal_env goal)) typ (goal_type goal) in
      fail4 "%s : %s does not exactly solve the goal %s (witness = %s)"
                    (tts (goal_env goal) t)
                    typ
                    goalt
                    (tts (goal_env goal) (goal_witness goal))))))))

let t_exact try_refine set_expected_typ tm : tac<unit> = wrap_err "exact" <|
    mlog (fun () -> BU.print1 "t_exact: tm = %s\n" (Print.term_to_string tm)) (fun _ ->
    bind (catch (__exact_now set_expected_typ tm)) (function
    | Inr r -> ret r
    | Inl e when not (try_refine) -> traise e
    | Inl e ->
        mlog (fun () -> BU.print_string "__exact_now failed, trying refine...\n") (fun _ ->
        bind (catch (bind (norm [EMB.Delta]) (fun _ ->
                       bind (refine_intro ()) (fun _ ->
                       __exact_now set_expected_typ tm)))) (function
              | Inr r ->
                  mlog (fun () -> BU.print_string "__exact_now: failed after refining too\n") (fun _ ->
                  ret r)
              | Inl _ ->
                  mlog (fun () -> BU.print_string "__exact_now: was not a refinement\n") (fun _ ->
                  traise e)))))

let rec  __try_unify_by_application
            (only_match : bool)
            (acc : list<(term * aqual * ctx_uvar)>)
            (e : env) (ty1 : term) (ty2 : term)
            (rng : Range.range)
            : tac<list<(term * aqual * ctx_uvar)>> =
    let f = if only_match
            then do_match
            else do_unify
    in
    bind (f e ty2 ty1) (function
    | true ->
        (* Done! *)
        ret acc
    | false -> begin
        (* Not a match, try instantiating the first type by application *)
        match U.arrow_one ty1 with
        | None ->
            fail2 "Could not instantiate, %s to %s" (term_to_string e ty1) (term_to_string e ty2)
        | Some (b, c) ->
            if not (U.is_total_comp c) then fail "Codomain is effectful" else
            bind (new_uvar "apply arg" e b.binder_bv.sort rng) (fun (uvt, uv) ->
            mlog (fun () -> BU.print1 "t_apply: generated uvar %s\n" (Print.ctx_uvar_to_string uv)) (fun _ ->
            let typ = U.comp_result c in
            let typ' = SS.subst [S.NT (b.binder_bv, uvt)] typ in
            __try_unify_by_application only_match ((uvt, b.binder_qual, uv)::acc) e typ' ty2 rng))
    end)

(* Can t1 unify t2 if it's applied to arguments? If so return uvars for them *)
(* NB: Result is reversed, which helps so we use fold_right instead of fold_left *)
let try_unify_by_application (only_match:bool) (e : env) (ty1 : term) (ty2 : term) (rng:Range.range) : tac<list<(term * aqual * ctx_uvar)>> =
    __try_unify_by_application only_match [] e ty1 ty2 rng

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
let t_apply (uopt:bool) (only_match:bool) (tm:term) : tac<unit> = wrap_err "apply" <|
    mlog (fun () -> BU.print1 "t_apply: tm = %s\n" (Print.term_to_string tm)) (fun _ ->
    bind cur_goal (fun goal ->
    let e = goal_env goal in
    mlog (fun () -> BU.print3 "t_apply: tm = %s\nt_apply: goal = %s\nenv.gamma=%s\n"
            (Print.term_to_string tm)
            (goal_to_string_verbose goal)
            (Env.print_gamma e.gamma)) (fun _ ->
    bind (__tc e tm) (fun (tm, typ, guard) ->
    // Focus helps keep the goal order
    let typ = bnorm e typ in
    bind (try_unify_by_application only_match e typ (goal_type goal) (rangeof goal)) (fun uvs ->
    mlog (fun () -> BU.print1 "t_apply: found args = %s\n"
        (FStar.Common.string_of_list (fun (t, _, _) -> Print.term_to_string t) uvs)) (fun () ->
    (* use normal implicit application for meta-args: meta application does not
     * make sense and the typechecker complains. *)
    let fix_qual q =
      match q with
      | Some (Meta _) -> Some (Implicit false)
      | _ -> q
    in
    let w = List.fold_right (fun (uvt, q, _) w -> U.mk_app w [(uvt, fix_qual q)]) uvs tm in

    let uvset = List.fold_right (fun (_, _, uv) s -> BU.set_union s (SF.uvars uv.ctx_uvar_typ)) uvs (SF.new_uv_set ()) in
    let free_in_some_goal uv =
        BU.set_mem uv uvset
    in
    bind (solve' goal w) (fun () ->
    bind (mapM (fun (uvt, q, uv) ->
                 match UF.find uv.ctx_uvar_head with
                 (* Already (at least partially) solved, skip asking the user for it *)
                 | Some _ ->
                       ret ()
                 (* Not instantiated at all *)
                 | None ->
                    (* We might still not add it if uopt is on, as described above *)
                    if uopt && free_in_some_goal uv
                    then ret ()
                    else add_goals [bnorm_goal ({ goal with
                                                  goal_ctx_uvar = uv;
                                                  is_guard = false; })]
               ) uvs) (fun _ ->
    proc_guard "apply guard" e guard (rangeof goal)
    ))))))))

// returns pre and post
let lemma_or_sq (c : comp) : option<(term * term)> =
    let ct = U.comp_to_comp_typ_nouniv c in
    if lid_equals ct.effect_name PC.effect_Lemma_lid then
        let pre, post = match ct.effect_args with
                        | pre::post::_ -> fst pre, fst post
                        | _ -> failwith "apply_lemma: impossible: not a lemma"
        in
        // Lemma post is thunked
        let post = U.mk_app post [S.as_arg U.exp_unit] in
        Some (pre, post)
    else if U.is_pure_effect ct.effect_name
         || U.is_ghost_effect ct.effect_name then
        map_opt (U.un_squash ct.result_typ) (fun post -> (U.t_true, post))
    else
        None

let rec fold_left (f : ('a -> 'b -> tac<'b>)) (e : 'b) (xs : list<'a>) : tac<'b> =
    match xs with
    | [] -> ret e
    | x::xs -> bind (f x e) (fun e' -> fold_left f e' xs)

let check_lemma_implicits_solution env (t:term) (k:typ) : guard_t =
  let env = Env.set_expected_typ ({env with use_bv_sorts=true}) k in

  let slow_path () =
    let must_tot = false in  //since we are typechecking lemma implicits
    //expected type is already set in the env
    let _, _, g = TcTerm.typeof_tot_or_gtot_term env t must_tot in
    g in

  match TcTerm.typeof_tot_or_gtot_term_fastpath env t false with
  | None -> slow_path ()
  | Some k' ->
    match Rel.subtype_nosmt env k' k with
    | None -> slow_path ()
    | Some g -> g

let t_apply_lemma (noinst:bool) (noinst_lhs:bool)
                  (tm:term) : tac<unit> = wrap_err "apply_lemma" <| focus (
    bind get (fun ps ->
    mlog (fun () -> BU.print1 "apply_lemma: tm = %s\n" (Print.term_to_string tm)) (fun _ ->
    let is_unit_t t = match (SS.compress t).n with
    | Tm_fvar fv when S.fv_eq_lid fv PC.unit_lid -> true
    | _ -> false
    in
    bind cur_goal (fun goal ->
    let env = goal_env goal in
    bind (__tc env tm) (fun (tm, t, guard) ->
    let bs, comp = U.arrow_formals_comp t in
    match lemma_or_sq comp with
    | None -> fail "not a lemma or squashed function"
    | Some (pre, post) ->
    bind (
       fold_left (fun ({binder_bv=b;binder_qual=aq}) (uvs, imps, subst) ->
               let b_t = SS.subst subst b.sort in
               if is_unit_t b_t
               then
                   // Simplification: if the argument is simply unit, then don't ask for it
                   ret <| ((U.exp_unit, aq)::uvs, imps, S.NT(b, U.exp_unit)::subst)
               else
                   bind (new_uvar "apply_lemma" env b_t (rangeof goal)) (fun (t, u) ->
                   ret <| ((t, aq)::uvs, (t, u)::imps, S.NT(b, t)::subst))
               )
       ([], [], [])
       bs)
    (fun (uvs, implicits, subst) ->
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
    bind (cmp_func env (goal_type goal) (U.mk_squash post_u post)) (fun b ->
    if not b
    then begin
        let post, goalt = TypeChecker.Err.print_discrepancy (tts env)
                                                            (U.mk_squash post_u post)
                                                            (goal_type goal) in
        fail3 "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                            (tts env tm) post goalt
    end else
        // We solve with (), we don't care about the witness if applying a lemma
        bind (solve' goal U.exp_unit) (fun _ ->
        let is_free_uvar uv t =
            let free_uvars = List.map (fun x -> x.ctx_uvar_head) (BU.set_elements (SF.uvars t)) in
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
        bind (implicits |> mapM (fun imp ->
            let (term, ctx_uvar) = imp in
            let hd, _ = U.head_and_args term in
            match (SS.compress hd).n with
            | Tm_uvar (ctx_uvar, _) ->
                let goal = bnorm_goal ({ goal with goal_ctx_uvar = ctx_uvar }) in
                ret [goal]
            | _ ->
                mlog (fun () -> BU.print2 "apply_lemma: arg %s unified to (%s)\n"
                                    (Print.uvar_to_string ctx_uvar.ctx_uvar_head)
                                    (Print.term_to_string term)) (fun () ->
                let g_typ =
                  // NS:01/24: use the fast path instead, knowing that term is at least well-typed
                  // NS:05/25: protecting it under this option,
                  //           since it causes a regression in examples/vale/*Math_i.fst
                  // GM: Made it the default, but setting must_total to true
                  // AR:03/17: These are lemma arguments, so we don't need to insist on must_total
                  check_lemma_implicits_solution env term ctx_uvar.ctx_uvar_typ
                in
                bind (proc_guard
                       (if ps.tac_verb_dbg
                        then BU.format2 "apply_lemma solved arg %s to %s\n" (Print.ctx_uvar_to_string ctx_uvar)
                                                                            (Print.term_to_string term)
                        else "apply_lemma solved arg")
                        env g_typ (rangeof goal)) (fun () ->
                ret [])))
            ) (fun sub_goals ->
        let sub_goals = List.flatten sub_goals in
        // Optimization: if a uvar appears in a later goal, don't ask for it, since
        // it will be instantiated later. It is tracked anyway in ps.implicits
        let rec filter' (f : 'a -> list<'a> -> bool) (xs : list<'a>) : list<'a> =
             match xs with
             | [] -> []
             | x::xs -> if f x xs then x::(filter' f xs) else filter' f xs
        in
        let sub_goals = filter' (fun g goals -> not (checkone (goal_witness g) goals)) sub_goals in
        bind (proc_guard "apply_lemma guard" env guard (rangeof goal)) (fun _ ->
        let pre_u = env.universe_of env pre in
        bind (match (Rel.simplify_guard env (Env.guard_of_guard_formula (NonTrivial pre))).guard_f with
              | Trivial -> ret ()
              | NonTrivial _ -> add_irrelevant_goal goal "apply_lemma precondition" env pre) //AR: should we use the normalized pre instead?
        
             (fun _ -> add_goals sub_goals)))))))))))

let split_env (bvar : bv) (e : env) : option<(env * bv * list<bv>)> =
    let rec aux e =
        match Env.pop_bv e with
        | None -> None
        | Some (bv', e') ->
            if S.bv_eq bvar bv'
            then Some (e', bv', [])
            else map_opt (aux e') (fun (e'', bv, bvs) -> (e'', bv, bv'::bvs ))
    in
    map_opt (aux e) (fun (e', bv, bvs) -> (e', bv, List.rev bvs))

let push_bvs e bvs =
    List.fold_left (fun e b -> Env.push_bv e b) e bvs

let subst_goal (b1 : bv) (b2 : bv) (g:goal) : tac<option<(bv * goal)>> =
    match split_env b1 (goal_env g) with
    | Some (e0, b1, bvs) ->
        let bs = List.map S.mk_binder (b1::bvs) in

        let t = goal_type g in

        (* Close the binders and t *)
        let bs', t' = SS.close_binders bs, SS.close bs t in

        (* Replace b1 (the head) by b2 *)
        let bs' = (S.mk_binder b2) :: List.tail bs' in

        (* Re-open, all done for renaming *)
        let bs'', t'' = SS.open_term bs' t' in

        (* b2 has been freshened *)
        let b2 = (List.hd bs'').binder_bv in

        (* Make a new goal in the new env (with new binders) *)
        let new_env = push_bvs e0 (List.map (fun b -> b.binder_bv) bs'') in
        bind (new_uvar "subst_goal" new_env t'' (rangeof g)) (fun (uvt, uv) ->
        let goal' = mk_goal new_env uv g.opts g.is_guard g.label in

        (* Solve the old goal with an application of the new witness *)
        let sol = U.mk_app (U.abs bs'' uvt None)
                            (List.map (fun ({binder_bv=bv;binder_qual=q}) -> S.as_arg (S.bv_to_name bv)) bs) in
        bind (set_solution g sol) (fun () ->

        ret (Some (b2, goal'))))

    | None ->
        ret None

let rewrite (h:binder) : tac<unit> = wrap_err "rewrite" <|
    bind cur_goal (fun goal ->
    let bv = h.binder_bv in
    mlog (fun _ -> BU.print2 "+++Rewrite %s : %s\n" (Print.bv_to_string bv) (Print.term_to_string bv.sort)) (fun _ ->
    match split_env bv (goal_env goal) with
    | None -> fail "binder not found in environment"
    | Some (e0, bv, bvs) ->
    begin match destruct_eq (whnf e0 bv.sort) with
        | Some (x, e) ->
        begin match (SS.compress x).n with
           | Tm_name x ->
             let s = [NT(x, e)] in

             (* See subst_goal for an explanation *)

             let t = goal_type goal in
             let bs = List.map S.mk_binder bvs in

             let bs', t' = SS.close_binders bs, SS.close bs t in

             let bs', t' = SS.subst_binders s bs', SS.subst s t' in

             let bs'', t'' = SS.open_term bs' t' in

             let new_env = push_bvs e0 (bv::(List.map (fun b -> b.binder_bv) bs'')) in

             bind (new_uvar "rewrite" new_env t'' (rangeof goal)) (fun (uvt, uv) ->
             let goal' = mk_goal new_env uv goal.opts goal.is_guard goal.label in
             let sol = U.mk_app (U.abs bs'' uvt None)
                                 (List.map (fun ({binder_bv=bv}) -> S.as_arg (S.bv_to_name bv)) bs) in

             (* See comment in subst_goal *)
             bind (set_solution goal sol) (fun () ->
             replace_cur goal'))
           | _ ->
             fail "Not an equality hypothesis with a variable on the LHS"
        end
        | _ -> fail "Not an equality hypothesis"
    end))

let rename_to (b : binder) (s : string) : tac<binder> = wrap_err "rename_to" <|
    bind cur_goal (fun goal ->
    let bv = b.binder_bv in
    let bv' = freshen_bv ({ bv with ppname = mk_ident (s, (range_of_id bv.ppname)) }) in
    bind (subst_goal bv bv' goal) (function
    | None -> fail "binder not found in environment"
    | Some (bv',  goal) ->
        bind (replace_cur goal) (fun () ->
        ret ({b with binder_bv=bv'}))))

let binder_retype (b : binder) : tac<unit> = wrap_err "binder_retype" <|
    bind cur_goal (fun goal ->
    let bv = b.binder_bv in
    match split_env bv (goal_env goal) with
    | None -> fail "binder is not present in environment"
    | Some (e0, bv, bvs) ->
        let (ty, u) = U.type_u () in
        bind (new_uvar "binder_retype" e0 ty (rangeof goal)) (fun (t', u_t') ->
        //NS: Question ... u_t' is dropped; why?
        //GM: No need for it... we just use t' which is approx (Tm_uvar u_t').
        //    The uvar is tracked in the proofstate too.
        let bv'' = {bv with sort = t'} in
        let s = [S.NT (bv, S.bv_to_name bv'')] in
        let bvs = List.map (fun b -> { b with sort = SS.subst s b.sort }) bvs in
        let env' = push_bvs e0 (bv''::bvs) in
        bind dismiss (fun _ ->
        let new_goal =
            goal_with_type
                (goal_with_env goal env')
                (SS.subst s (goal_type goal))
        in
        bind (add_goals [new_goal]) (fun _ ->
              add_irrelevant_goal goal "binder_retype equation" e0
                  (U.mk_eq2 (U_succ u) ty bv.sort t'))))
    )

(* TODO: move to bv *)
let norm_binder_type (s : list<EMB.norm_step>) (b : binder) : tac<unit> = wrap_err "norm_binder_type" <|
    bind cur_goal (fun goal ->
    let bv = b.binder_bv in
    match split_env bv (goal_env goal) with
    | None -> fail "binder is not present in environment"
    | Some (e0, bv, bvs) -> begin
        let steps = [Env.Reify; Env.UnfoldTac]@(N.tr_norm_steps s) in
        let sort' = normalize steps e0 bv.sort in
        let bv' = { bv with sort = sort' } in
        let env' = push_bvs e0 (bv'::bvs) in
        replace_cur (goal_with_env goal env')
        end
    )

let revert () : tac<unit> =
    bind cur_goal (fun goal ->
    match Env.pop_bv (goal_env goal) with
    | None -> fail "Cannot revert; empty context"
    | Some (x, env') ->
        let typ' = U.arrow [S.mk_binder x] (mk_Total (goal_type goal)) in
        bind (new_uvar "revert" env' typ' (rangeof goal)) (fun (r, u_r) ->
        bind (set_solution goal (S.mk_Tm_app r [S.as_arg (S.bv_to_name x)] (goal_type goal).pos)) (fun () ->
        let g = mk_goal env' u_r goal.opts goal.is_guard goal.label in
        replace_cur g)))

let free_in bv t =
    Util.set_mem bv (SF.names t)

let clear (b : binder) : tac<unit> =
    let bv = b.binder_bv in
    bind cur_goal (fun goal ->
    mlog (fun () -> BU.print2 "Clear of (%s), env has %s binders\n"
                        (Print.binder_to_string b)
                        (Env.all_binders (goal_env goal) |> List.length |> string_of_int)) (fun () ->
    match split_env bv (goal_env goal) with
    | None -> fail "Cannot clear; binder not in environment"
    | Some (e', bv, bvs) ->
        let rec check bvs =
            match bvs with
            | [] -> ret ()
            | bv'::bvs ->
                if free_in bv bv'.sort
                then fail (BU.format1 "Cannot clear; binder present in the type of %s"
                                    (Print.bv_to_string bv'))
                else check bvs
        in
        if free_in bv (goal_type goal) then
            fail "Cannot clear; binder present in goal"
        else bind (check bvs) (fun () ->
        let env' = push_bvs e' bvs in
        bind (new_uvar "clear.witness" env' (goal_type goal) (rangeof goal)) (fun (ut, uvar_ut) ->
        bind (set_solution goal ut) (fun () ->
        replace_cur (mk_goal env' uvar_ut goal.opts goal.is_guard goal.label))))))

let clear_top () : tac<unit> =
    bind cur_goal (fun goal ->
    match Env.pop_bv (goal_env goal) with
    | None -> fail "Cannot clear; empty context"
    | Some (x, _) -> clear (S.mk_binder x)) // we ignore the qualifier anyway

let prune (s:string) : tac<unit> =
    bind cur_goal (fun g ->
    let ctx = goal_env g in
    let ctx' = Env.rem_proof_ns ctx (path_of_text s) in
    let g' = goal_with_env g ctx' in
    replace_cur g')

let addns (s:string) : tac<unit> =
    bind cur_goal (fun g ->
    let ctx = goal_env g in
    let ctx' = Env.add_proof_ns ctx (path_of_text s) in
    let g' = goal_with_env g ctx' in
    replace_cur g')

let guard_formula (g:guard_t) : term =
  match g.guard_f with
  | Trivial -> U.t_true
  | NonTrivial f -> f

let _t_trefl (allow_guards:bool) (l : term) (r : term) : tac<unit> =
  bind cur_goal (fun g ->
  let attempt (l : term) (r : term) : tac<bool> =
    bind (do_unify' allow_guards (goal_env g) l r) (function
    | None -> ret false
    | Some guard ->
      bind (solve' g U.exp_unit) (fun _ ->
      if allow_guards
      then
        bind (goal_of_guard "t_trefl" (goal_env g) (guard_formula guard) (rangeof g)) (fun goal ->
        bind (push_goals [goal]) (fun _ ->
        ret true))
      else
        // If allow_guards is false, this guard must be trivial and we don't
        // add it, but we check its triviality for sanity.
        if Env.is_trivial_guard_formula guard
        then ret true
        else failwith "internal error: _t_refl: guard is not trivial"
      ))
  in
  bind (attempt l r) (function
  | true -> ret ()
  | false ->
      (* if that didn't work, normalize and retry *)
      let norm = N.normalize [Env.UnfoldUntil delta_constant; Env.Primops; Env.UnfoldTac] (goal_env g) in
      bind (attempt (norm l) (norm r)) (function
      | true -> ret ()
      | false ->
        let ls, rs = TypeChecker.Err.print_discrepancy (tts (goal_env g)) l r in
        fail2 "cannot unify (%s) and (%s)" ls rs)))

let t_trefl (allow_guards:bool) : tac<unit> = wrap_err "t_trefl" <|
    bind cur_goal (fun g ->
    match destruct_eq (whnf (goal_env g) (goal_type g)) with
    | Some (l, r) ->
        _t_trefl allow_guards l r
    | None ->
        fail1 "not an equality (%s)" (tts (goal_env g) (goal_type g)))

let dup () : tac<unit> =
    bind cur_goal (fun g ->
    let env = goal_env g in
    bind (new_uvar "dup" env (goal_type g) (rangeof g)) (fun (u, u_uvar) ->
    let g' = { g with goal_ctx_uvar = u_uvar } in
    bind dismiss (fun _ ->
    let t_eq = U.mk_eq2 (env.universe_of env (goal_type g)) (goal_type g) u (goal_witness g) in
    bind (add_irrelevant_goal g "dup equation" env t_eq) (fun _ ->
    bind (add_goals [g']) (fun _ ->
    ret ())))))

// longest_prefix f l1 l2 = (p, r1, r2) ==> l1 = p@r1 /\ l2 = p@r2
let longest_prefix (f : 'a -> 'a -> bool) (l1 : list<'a>) (l2 : list<'a>) : list<'a> * list<'a> * list<'a> =
    let rec aux acc l1 l2 =
        match l1, l2 with
        | x::xs, y::ys ->
            if f x y
            then aux (x::acc) xs ys
            else acc, xs, ys
        | _ ->
            acc, l1, l2
    in
    let pr, t1, t2 = aux [] l1 l2 in
    List.rev pr, t1, t2


// fix universes
let join_goals g1 g2 : tac<goal> =
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
    let gamma, r1, r2 = longest_prefix S.eq_binding (List.rev gamma1) (List.rev gamma2) in

    let t1 = close_forall_no_univs (Env.binders_of_bindings (List.rev r1)) phi1 in
    let t2 = close_forall_no_univs (Env.binders_of_bindings (List.rev r2)) phi2 in

    bind (set_solution g1 U.exp_unit) (fun () ->
    bind (set_solution g2 U.exp_unit) (fun () ->

    let ng = U.mk_conj t1 t2 in
    let nenv = { goal_env g1 with gamma = List.rev gamma
                                ; gamma_cache = BU.smap_create 100 (* Paranoid? *)
                                } in
    bind (mk_irrelevant_goal "joined" nenv ng (rangeof g1) g1.opts g1.label) (fun goal ->
    mlog (fun () -> BU.print3 "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                (goal_to_string_verbose g1)
                (goal_to_string_verbose g2)
                (goal_to_string_verbose goal)) (fun () ->
    ret goal))))

let join () : tac<unit> =
    bind get (fun ps ->
    match ps.goals with
    | g1::g2::gs ->
        bind (set ({ ps with goals = gs })) (fun () ->
        bind (join_goals g1 g2) (fun g12 ->
        add_goals [g12]))

    | _ -> fail "join: less than 2 goals"
    )

let set_options (s : string) : tac<unit> = wrap_err "set_options" <|
    bind cur_goal (fun g ->
    FStar.Options.push ();
    FStar.Options.set (Util.smap_copy g.opts); // copy the map, they are not purely functional
    let res = FStar.Options.set_options s in
    let opts' = FStar.Options.peek () in
    FStar.Options.pop ();
    match res with
    | FStar.Getopt.Success ->
        let g' = { g with opts = opts' } in
        replace_cur g'
    | FStar.Getopt.Error err ->
        fail2 "Setting options `%s` failed: %s" s err
    | FStar.Getopt.Help ->
        fail1 "Setting options `%s` failed (got `Help`?)" s
    )

let top_env     () : tac<env>  = bind get (fun ps -> ret <| ps.main_context)

let lax_on () : tac<bool> =
    bind cur_goal (fun g ->
    ret (Options.lax () || (goal_env g).lax))

let unquote (ty : term) (tm : term) : tac<term> = wrap_err "unquote" <|
    mlog (fun () -> BU.print1 "unquote: tm = %s\n" (Print.term_to_string tm)) (fun _ ->
    bind cur_goal (fun goal ->
    let env = Env.set_expected_typ (goal_env goal) ty in
    bind (__tc_ghost env tm) (fun (tm, typ, guard) ->
    mlog (fun () -> BU.print1 "unquote: tm' = %s\n" (Print.term_to_string tm)) (fun _ ->
    mlog (fun () -> BU.print1 "unquote: typ = %s\n" (Print.term_to_string typ)) (fun _ ->
    bind (proc_guard "unquote" env guard (rangeof goal)) (fun () ->
    ret tm))))))

let uvar_env (env : env) (ty : option<typ>) : tac<term> =
    bind get (fun ps ->
    // If no type was given, add a uvar for it too!
    bind
        (match ty with
        | Some ty ->
          ret ty

        | None ->
          bind (new_uvar "uvar_env.2" env (fst <| U.type_u ()) ps.entry_range)
              (fun (typ, uvar_typ) -> //NS, FIXME discarding uvar_typ
                   ret typ)
        )
        (fun typ ->
            bind (new_uvar "uvar_env" env typ ps.entry_range) (fun (t, uvar_t) ->
            ret t)))

let unshelve (t : term) : tac<unit> = wrap_err "unshelve" <|
    bind get (fun ps ->
    let env = ps.main_context in
    (* We need a set of options, but there might be no goals, so do this *)
    let opts = match ps.goals with
               | g::_ -> g.opts
               | _ -> FStar.Options.peek ()
    in
    match U.head_and_args t with
    | { n = Tm_uvar (ctx_uvar, _) }, _ ->
        let env = {env with gamma=ctx_uvar.ctx_uvar_gamma} in
        let g = mk_goal env ctx_uvar opts false "" in
        add_goals [bnorm_goal g]
    | _ -> fail "not a uvar")

let tac_and (t1 : tac<bool>) (t2 : tac<bool>) : tac<bool> =
    let comp = bind t1 (fun b ->
               bind (if b then t2 else ret false) (fun b' ->
               if b'
               then ret b'
               else fail ""))
    in
    bind (trytac comp) (function
    | Some true -> ret true
    | Some false -> failwith "impossible"
    | None -> ret false)


let match_env (e:env) (t1 : term) (t2 : term) : tac<bool> = wrap_err "match_env" <|
    bind get (fun ps ->
    bind (__tc e t1) (fun (t1, ty1, g1) ->
    bind (__tc e t2) (fun (t2, ty2, g2) ->
    bind (proc_guard "match_env g1" e g1 ps.entry_range) (fun () ->
    bind (proc_guard "match_env g2" e g2 ps.entry_range) (fun () ->
    tac_and (do_match e ty1 ty2) (do_match e t1 t2))))))

let unify_env (e:env) (t1 : term) (t2 : term) : tac<bool> = wrap_err "unify_env" <|
    bind get (fun ps ->
    bind (__tc e t1) (fun (t1, ty1, g1) ->
    bind (__tc e t2) (fun (t2, ty2, g2) ->
    bind (proc_guard "unify_env g1" e g1 ps.entry_range) (fun () ->
    bind (proc_guard "unify_env g2" e g2 ps.entry_range) (fun () ->
    tac_and (do_unify e ty1 ty2) (do_unify e t1 t2))))))

let unify_guard_env (e:env) (t1 : term) (t2 : term) : tac<bool> = wrap_err "unify_guard_env" <|
    bind get (fun ps ->
    bind (__tc e t1) (fun (t1, ty1, g1) ->
    bind (__tc e t2) (fun (t2, ty2, g2) ->
    bind (proc_guard "unify_guard_env g1" e g1 ps.entry_range) (fun () ->
    bind (proc_guard "unify_guard_env g2" e g2 ps.entry_range) (fun () ->
    bind (do_unify' true e ty1 ty2) (function
    | None -> ret false
    | Some g1 ->
      bind (do_unify' true e t1 t2) (function
      | None -> ret false
      | Some g2 ->
        let formula : term = U.mk_conj (guard_formula g1) (guard_formula g2) in
        bind (goal_of_guard "unify_guard_env.g2" e formula ps.entry_range) (fun goal ->
        bind (push_goals [goal]) (fun _ ->
        ret true)))))))))

let launch_process (prog : string) (args : list<string>) (input : string) : tac<string> =
    // The `bind idtac` thunks the tactic
    bind idtac (fun () ->
    if Options.unsafe_tactic_exec () then
        let s = BU.run_process "tactic_launch" prog args (Some input) in
        ret s
    else
        fail "launch_process: will not run anything unless --unsafe_tactic_exec is provided"
    )

let fresh_bv_named (nm : string) (t : typ) : tac<bv> =
    // The `bind idtac` thunks the tactic. Not really needed, just being paranoid
    bind idtac (fun () ->
        ret (gen_bv nm None t)
    )

let change (ty : typ) : tac<unit> = wrap_err "change" <|
    mlog (fun () -> BU.print1 "change: ty = %s\n" (Print.term_to_string ty)) (fun _ ->
    bind cur_goal (fun g ->
    bind (__tc (goal_env g) ty) (fun (ty, _, guard) ->
    bind (proc_guard "change" (goal_env g) guard (rangeof g)) (fun () ->
    bind (do_unify (goal_env g) (goal_type g) ty) (fun bb ->
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
        bind (do_unify (goal_env g) ng nty) (fun b ->
        if b
        then replace_cur (goal_with_type g ty)
        else fail "not convertible")
    end)))))

let failwhen (b:bool) (msg:string) (k:unit -> tac<'a>) : tac<'a> =
    if b
    then fail msg
    else k ()

let t_destruct (s_tm : term) : tac<list<(fv * Z.t)>> = wrap_err "destruct" <|
    bind cur_goal (fun g ->
    bind (__tc (goal_env g) s_tm) (fun (s_tm, s_ty, guard) ->
    bind (proc_guard "destruct" (goal_env g) guard (rangeof g)) (fun () ->
    let s_ty = N.normalize [Env.UnfoldTac; Env.Weak; Env.HNF; Env.UnfoldUntil delta_constant]
                           (goal_env g) s_ty in
    let h, args = U.head_and_args_full (U.unrefine s_ty) in
    bind (match (SS.compress h).n with
          | Tm_fvar fv -> ret (fv, [])
          | Tm_uinst ({ n = Tm_fvar fv }, us) -> ret (fv, us)
          | _ -> fail "type is not an fv") (fun (fv, a_us) ->
    let t_lid = lid_of_fv fv in
    match Env.lookup_sigelt (goal_env g) t_lid with
    | None -> fail "type not found in environment"
    | Some se ->
    match se.sigel with
    | Sig_inductive_typ (_lid, t_us, t_ps, t_ty, mut, c_lids) ->
      (* High-level idea of this huge function:
       * For  Gamma |- w : phi  and  | C : ps -> bs -> t,  we generate a new goal
       *   Gamma |- w' : bs -> phi
       * with
       *   w = match tm with ... | C .ps' bs' -> w' bs' ...
       * i.e., we do not intro the matched binders and let the
       * user do that (with the returned arity). `.ps` represents inaccesible patterns
       * for the type's parameters.
       *)
      let erasable = U.has_attribute se.sigattrs FStar.Parser.Const.erasable_attr in
      failwhen (erasable && not (is_irrelevant g)) "cannot destruct erasable type to solve proof-relevant goal" (fun () ->

      (* Instantiate formal universes to the actuals,
       * and substitute accordingly in binders and types *)
      failwhen (List.length a_us <> List.length t_us) "t_us don't match?" (fun () ->


      (* Not needed currently? *)
      (* let s = Env.mk_univ_subst t_us a_us in *)
      (* let t_ps = SS.subst_binders s t_ps in *)
      (* let t_ty = SS.subst         s t_ty in *)
      let t_ps, t_ty = SS.open_term t_ps t_ty in

      bind (mapM (fun c_lid ->
                    match Env.lookup_sigelt (goal_env g) c_lid with
                    | None -> fail "ctor not found?"
                    | Some se ->
                    match se.sigel with
                    | Sig_datacon (_c_lid, c_us, c_ty, _t_lid, nparam, mut) ->
                        (* BU.print2 "ty of %s = %s\n" (Ident.string_of_lid c_lid) *)
                        (*                             (Print.term_to_string c_ty); *)
                        let fv = S.lid_as_fv c_lid S.delta_constant (Some Data_ctor) in


                        failwhen (List.length a_us <> List.length c_us) "t_us don't match?" (fun () ->
                        let s = Env.mk_univ_subst c_us a_us in
                        let c_ty = SS.subst s c_ty in

                        (* The constructor might be universe-polymorphic, just use
                         * fresh univ_uvars for its universes. *)
                        let c_us, c_ty = Env.inst_tscheme (c_us, c_ty) in

                        (* BU.print2 "ty(2) of %s = %s\n" (Ident.string_of_lid c_lid) *)
                        (*                                (Print.term_to_string c_ty); *)

                        (* Deconstruct its type, separating the parameters from the
                         * actual arguments (indices do not matter here). *)
                        let bs, comp = U.arrow_formals_comp c_ty in

                        (* More friendly names: 'a_i' instead of '_i' *)
                        let bs, comp =
                          let rename_bv bv =
                              let ppname = bv.ppname in
                              let ppname = mk_ident ("a" ^ string_of_id ppname, range_of_id ppname) in
                              // freshen just to be extra safe.. probably not needed
                              freshen_bv ({ bv with ppname = ppname })
                          in
                          let bs' = List.map (fun b -> {b with binder_bv=rename_bv b.binder_bv}) bs in
                          let subst = List.map2 (fun ({binder_bv=bv}) ({binder_bv=bv'}) -> NT (bv, bv_to_name bv')) bs bs' in
                          SS.subst_binders subst bs', SS.subst_comp subst comp
                        in

                        (* BU.print1 "bs = (%s)\n" (Print.binders_to_string ", " bs); *)
                        let d_ps, bs = List.splitAt nparam bs in
                        failwhen (not (U.is_total_comp comp)) "not total?" (fun () ->
                        let mk_pat p = { v = p; p = s_tm.pos } in
                        (* TODO: This is silly, why don't we just keep aq in the Pat_cons? *)
                        let is_imp = function | Some (Implicit _) -> true
                                              | _ -> false
                        in
                        let a_ps, a_is = List.splitAt nparam args in
                        failwhen (List.length a_ps <> List.length d_ps) "params not match?" (fun () ->
                        let d_ps_a_ps = List.zip d_ps a_ps in
                        let subst = List.map (fun (({binder_bv=bv}), (t, _)) -> NT (bv, t)) d_ps_a_ps in
                        let bs = SS.subst_binders subst bs in
                        let subpats_1 = List.map (fun (({binder_bv=bv}), (t, _)) ->
                                                 (mk_pat (Pat_dot_term (bv, t)), true)) d_ps_a_ps in
                        let subpats_2 = List.map (fun ({binder_bv=bv;binder_qual=aq}) ->
                                                 (mk_pat (Pat_var bv), is_imp aq)) bs in
                        let subpats = subpats_1 @ subpats_2 in
                        let pat = mk_pat (Pat_cons (fv, subpats)) in
                        let env = (goal_env g) in


                        (* Add an argument stating the equality between the scrutinee
                         * and the pattern, in-scope for this branch. *)
                        let cod = goal_type g in
                        let equ = env.universe_of env s_ty in
                        (* Typecheck the pattern, to fill-in the universes and get an expression out of it *)
                        let _ , _, _, _, pat_t, _, _guard_pat, _erasable = TcTerm.tc_pat ({ env with lax = true }) s_ty pat in
                        let eq_b = S.gen_bv "breq" None (U.mk_squash equ (U.mk_eq2 equ s_ty s_tm pat_t)) in
                        let cod = U.arrow [S.mk_binder eq_b] (mk_Total cod) in

                        let nty = U.arrow bs (mk_Total cod) in
                        bind (new_uvar "destruct branch" env nty (rangeof g)) (fun (uvt, uv) ->
                        let g' = mk_goal env uv g.opts false g.label in
                        let brt = U.mk_app_binders uvt bs in
                        (* Provide the scrutinee equality, which is trivially provable *)
                        let brt = U.mk_app brt [S.as_arg U.exp_unit] in
                        let br = SS.close_branch (pat, None, brt) in
                        ret (g', br, (fv, Z.of_int_fs (List.length bs)))))))
                    | _ ->
                        fail "impossible: not a ctor")
                 c_lids) (fun goal_brs ->
      let goals, brs, infos = List.unzip3 goal_brs in
      let w = mk (Tm_match (s_tm, None, brs)) s_tm.pos in
      bind (solve' g w) (fun () ->
      bind (add_goals goals) (fun () ->
      ret infos)))))

    | _ -> fail "not an inductive type"))))

// TODO: move to library?
let rec last (l:list<'a>) : 'a =
    match l with
    | [] -> failwith "last: empty list"
    | [x] -> x
    | _::xs -> last xs

let rec init (l:list<'a>) : list<'a> =
    match l with
    | [] -> failwith "init: empty list"
    | [x] -> []
    | x::xs -> x :: init xs

(* TODO: these are mostly duplicated from FStar.Reflection.Basic, unify *)
let rec inspect (t:term) : tac<term_view> = wrap_err "inspect" (
    bind (top_env ()) (fun e ->
    let t = U.unascribe t in
    let t = U.un_uinst t in
    let t = U.unlazy_emb t in
    match t.n with
    | Tm_meta (t, _) ->
        inspect t

    | Tm_name bv ->
        ret <| Tv_Var bv

    | Tm_bvar bv ->
        ret <| Tv_BVar bv

    | Tm_fvar fv ->
        ret <| Tv_FVar fv

    | Tm_app (hd, []) ->
        failwith "empty arguments on Tm_app"

    | Tm_app (hd, args) ->
        // We split at the last argument, since the term_view does not
        // expose n-ary lambdas buy unary ones.
        let (a, q) = last args in
        let q' = inspect_aqual q in
        ret <| Tv_App (S.mk_Tm_app hd (init args) t.pos, (a, q')) // TODO: The range and tk are probably wrong. Fix

    | Tm_abs ([], _, _) ->
        failwith "empty arguments on Tm_abs"

    | Tm_abs (bs, t, k) ->
        let bs, t = SS.open_term bs t in
        // `let b::bs = bs` gives a coverage warning, avoid it
        begin match bs with
        | [] -> failwith "impossible"
        | b::bs -> ret <| Tv_Abs (b, U.abs bs t k)
        end

    | Tm_type _ ->
        ret <| Tv_Type ()

    | Tm_arrow ([], k) ->
        failwith "empty binders on arrow"

    | Tm_arrow _ ->
        begin match U.arrow_one t with
        | Some (b, c) -> ret <| Tv_Arrow (b, c)
        | None -> failwith "impossible"
        end

    | Tm_refine (bv, t) ->
        let b = S.mk_binder bv in
        let b', t = SS.open_term [b] t in
        // `let [b] = b'` gives a coverage warning, avoid it
        let b = (match b' with
        | [b'] -> b'
        | _ -> failwith "impossible") in
        ret <| Tv_Refine (b.binder_bv, t)

    | Tm_constant c ->
        ret <| Tv_Const (inspect_const c)

    | Tm_uvar (ctx_u, s) ->
        ret <| Tv_Uvar (Z.of_int_fs (UF.uvar_id ctx_u.ctx_uvar_head), (ctx_u, s))

    | Tm_let ((false, [lb]), t2) ->
        if lb.lbunivs <> [] then ret <| Tv_Unknown else
        begin match lb.lbname with
        | Inr _ -> ret <| Tv_Unknown // no top level lets
        | Inl bv ->
            // The type of `bv` should match `lb.lbtyp`
            let b = S.mk_binder bv in
            let bs, t2 = SS.open_term [b] t2 in
            let b = match bs with
                    | [b] -> b
                    | _ -> failwith "impossible: open_term returned different amount of binders"
            in
            ret <| Tv_Let (false, lb.lbattrs, b.binder_bv, lb.lbdef, t2)
        end

    | Tm_let ((true, [lb]), t2) ->
        if lb.lbunivs <> [] then ret <| Tv_Unknown else
        begin match lb.lbname with
        | Inr _ -> ret <| Tv_Unknown // no top level lets
        | Inl bv ->
            let lbs, t2 = SS.open_let_rec [lb] t2 in
            match lbs with
            | [lb] ->
                (match lb.lbname with
                 | Inr _ -> ret Tv_Unknown
                 | Inl bv -> ret <| Tv_Let (true, lb.lbattrs, bv, lb.lbdef, t2))
            | _ -> failwith "impossible: open_term returned different amount of binders"
        end

    | Tm_match (t, ret_opt, brs) ->
        let rec inspect_pat p =
            match p.v with
            | Pat_constant c -> Pat_Constant (inspect_const c)
            | Pat_cons (fv, ps) -> Pat_Cons (fv, List.map (fun (p, b) -> inspect_pat p, b) ps)
            | Pat_var bv -> Pat_Var bv
            | Pat_wild bv -> Pat_Wild bv
            | Pat_dot_term (bv, t) -> Pat_Dot_Term (bv, t)
        in
        let brs = List.map SS.open_branch brs in
        let brs = List.map (function (pat, _, t) -> (inspect_pat pat, t)) brs in
        ret <| Tv_Match (t, ret_opt, brs)

    | Tm_unknown ->
        ret <| Tv_Unknown

    | _ ->
        Err.log_issue t.pos (Err.Warning_CantInspect, BU.format2 "inspect: outside of expected syntax (%s, %s)\n" (Print.tag_of_term t) (term_to_string e t));
        ret <| Tv_Unknown
    ))

(* This function could actually be pure, it doesn't need freshness
 * like `inspect` does, but we mark it as Tac for uniformity. *)
let pack (tv:term_view) : tac<term> =
    match tv with
    | Tv_Var bv ->
        ret <| S.bv_to_name bv

    | Tv_BVar bv ->
        ret <| S.bv_to_tm bv

    | Tv_FVar fv ->
        ret <| S.fv_to_tm fv

    | Tv_App (l, (r, q)) ->
        let q' = pack_aqual q in
        ret <| U.mk_app l [(r, q')]

    | Tv_Abs (b, t) ->
        ret <| U.abs [b] t None // TODO: effect?

    | Tv_Arrow (b, c) ->
        ret <| U.arrow [b] c

    | Tv_Type () ->
        ret <| U.ktype

    | Tv_Refine (bv, t) ->
        ret <| U.refine bv t

    | Tv_Const c ->
        ret <| S.mk (Tm_constant (pack_const c)) Range.dummyRange

    | Tv_Uvar (_u, ctx_u_s) ->
        ret <| S.mk (Tm_uvar ctx_u_s) Range.dummyRange

    | Tv_Let (false, attrs, bv, t1, t2) ->
        let lb = U.mk_letbinding (Inl bv) [] bv.sort PC.effect_Tot_lid t1 attrs Range.dummyRange in
        ret <| S.mk (Tm_let ((false, [lb]), SS.close [S.mk_binder bv] t2)) Range.dummyRange

    | Tv_Let (true, attrs, bv, t1, t2) ->
        let lb = U.mk_letbinding (Inl bv) [] bv.sort PC.effect_Tot_lid t1 attrs Range.dummyRange in
        let lbs, body = SS.close_let_rec [lb] t2 in
        ret <| S.mk (Tm_let ((true, lbs), body)) Range.dummyRange

    | Tv_Match (t, ret_opt, brs) ->
        let wrap v = {v=v;p=Range.dummyRange} in
        let rec pack_pat p : S.pat =
            match p with
            | Pat_Constant c -> wrap <| Pat_constant (pack_const c)
            | Pat_Cons (fv, ps) -> wrap <| Pat_cons (fv, List.map (fun (p, b) -> pack_pat p, b) ps)
            | Pat_Var  bv -> wrap <| Pat_var bv
            | Pat_Wild bv -> wrap <| Pat_wild bv
            | Pat_Dot_Term (bv, t) -> wrap <| Pat_dot_term (bv, t)
        in
        let brs = List.map (function (pat, t) -> (pack_pat pat, None, t)) brs in
        let brs = List.map SS.close_branch brs in
        ret <| S.mk (Tm_match (t, ret_opt, brs)) Range.dummyRange

    | Tv_AscribedT(e, t, tacopt) ->
        ret <| S.mk (Tm_ascribed(e, (Inl t, tacopt), None)) Range.dummyRange

    | Tv_AscribedC(e, c, tacopt) ->
        ret <| S.mk (Tm_ascribed(e, (Inr c, tacopt), None)) Range.dummyRange

    | Tv_Unknown ->
        ret <| S.mk Tm_unknown Range.dummyRange

let lget (ty:term) (k:string) : tac<term> = wrap_err "lget" <|
    bind get (fun ps ->
    match BU.psmap_try_find ps.local_state k with
    | None -> fail "not found"
    | Some t -> unquote ty t
    )

let lset (_ty:term) (k:string) (t:term) : tac<unit> = wrap_err "lset" <|
    bind get (fun ps ->
    let ps = { ps with local_state = BU.psmap_add ps.local_state k t } in
    set ps)

let set_urgency (u:Z.t) : tac<unit> =
    bind get (fun ps ->
    let ps = { ps with urgency = Z.to_int_fs u } in
    set ps)

let t_commute_applied_match () : tac<unit> = wrap_err "t_commute_applied_match" <|
  bind cur_goal (fun g ->
  match destruct_eq (whnf (goal_env g) (goal_type g)) with
  | Some (l, r) -> begin
    let lh, las = U.head_and_args_full l in
    match (SS.compress (U.unascribe lh)).n with
    | Tm_match (e, asc_opt, brs) ->
      let brs' = List.map (fun (p, w, e) -> p, w, U.mk_app e las) brs in
      let l' = mk (Tm_match (e, asc_opt, brs')) l.pos in
      bind (do_unify' false (goal_env g) l' r) (function
      | None -> fail "discharging the equality failed"
      | Some guard ->
        if Env.is_trivial_guard_formula guard
        then solve g U.exp_unit
        else failwith "internal error: _t_refl: guard is not trivial")
    | _ ->
      fail "lhs is not a match"
    end
  | None ->
    fail "not an equality")

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
        depth = 0;
        __dump = do_dump_proofstate;
        psc = Cfg.null_psc;
        entry_range = rng;
        guard_policy = SMT;
        freshness = 0;
        tac_verb_dbg = Env.debug env (Options.Other "TacVerbose");
        local_state = BU.psmap_empty ();
        urgency = 1;
    }
    in
    ps

let proofstate_of_goal_ty rng env typ =
    let env = tac_env env in
    let g, g_u = goal_of_goal_ty env typ in
    let ps = proofstate_of_goals rng env [g] g_u.implicits in
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
        depth = 0;
        __dump = (fun ps msg -> do_dump_proofstate ps msg);
        psc = Cfg.null_psc;
        entry_range = rng;
        guard_policy = SMT;
        freshness = 0;
        tac_verb_dbg = Env.debug env (Options.Other "TacVerbose");
        local_state = BU.psmap_empty ();
        urgency = 1;
    }
    in
    (ps, w)

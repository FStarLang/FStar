#light "off"
module FStar.Tactics.Basic
open FStar
open FStar.ST
open FStar.Exn
open FStar.All
open FStar.Syntax.Syntax
open FStar.Util
open FStar.Ident
open FStar.TypeChecker.Env

module SP = FStar.Syntax.Print
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module SF = FStar.Syntax.Free
module PC = FStar.Parser.Const
module U = FStar.Syntax.Util
module BU = FStar.Util
module Env = FStar.TypeChecker.Env
module Rel = FStar.TypeChecker.Rel
module Print = FStar.Syntax.Print
module TcUtil = FStar.TypeChecker.Util
module TcTerm = FStar.TypeChecker.TcTerm
module TcComm = FStar.TypeChecker.Common
module Cfg = FStar.TypeChecker.Cfg
module N = FStar.TypeChecker.Normalize
module UF = FStar.Syntax.Unionfind
module EMB = FStar.Syntax.Embeddings
module Err = FStar.Errors
module Z = FStar.BigInt
module Env = FStar.TypeChecker.Env
open FStar.Reflection.Data
open FStar.Reflection.Basic
open FStar.Tactics.Result
open FStar.Tactics.Types

type name = bv
type env = Env.env
type implicits = Env.implicits

// Beta reduce
let normalize s e t = N.normalize_with_primitive_steps FStar.Reflection.Interpreter.reflection_primops s e t
let bnorm e t = normalize [] e t

(* Use this one for everything the user is supposed to see, as it does resugaring.
 * For debug messages, just use plain term_to_string, we don't want to cause normalization with debug flags. *)
let tts = N.term_to_string

let bnorm_goal g = goal_with_type g (bnorm (goal_env g) (goal_type g))

(* The main monad for tactics.
 * A record, so we can keep it somewhat encapsulated and
 * can more easily add things to it if need be.
 *)
type tac<'a> = {
    tac_f : proofstate -> __result<'a>;
}

let mk_tac (f : proofstate -> __result<'a>) : tac<'a> =
    { tac_f = f }

let run t p =
    t.tac_f p

let run_safe t p =
    if Options.tactics_failhard ()
    then run t p
    else try run t p
    with | Errors.Err (_, msg)
         | Errors.Error (_, msg, _) -> Failed (TacticFailure msg, p)
         | e -> Failed (e, p)

let rec log ps (f : unit -> unit) : unit =
    if ps.tac_verb_dbg
    then f ()
    else ()

(* monadic return *)
let ret (x:'a) : tac<'a> =
    mk_tac (fun p -> Success (x, p))

(* monadic bind *)
let bind (t1:tac<'a>) (t2:'a -> tac<'b>) : tac<'b> =
    mk_tac (fun p ->
            match run t1 p with
            | Success (a, q)  -> run (t2 a) q
            | Failed (msg, q) -> Failed (msg, q))

(* get : get the current proof state *)
let get : tac<proofstate> =
    mk_tac (fun p -> Success (p, p))

let idtac : tac<unit> = ret ()

let get_uvar_solved uv =
    match FStar.Syntax.Unionfind.find uv.ctx_uvar_head with
    | Some t -> Some t
    | None   -> None

let check_goal_solved goal = get_uvar_solved goal.goal_ctx_uvar

let goal_to_string_verbose (g:goal) : string =
    BU.format2 "%s%s\n"
        (Print.ctx_uvar_to_string g.goal_ctx_uvar)
        (match check_goal_solved g with
         | None -> ""
         | Some t -> BU.format1 "\tGOAL ALREADY SOLVED!: %s" (Print.term_to_string t))

let goal_to_string (kind : string) (maybe_num : option<(int * int)>) (ps:proofstate) (g:goal) : string =
    let w =
        if Options.print_implicits ()
        then tts (goal_env g) (goal_witness g)
        else match get_uvar_solved g.goal_ctx_uvar with
             | None -> "_"
             | Some t -> tts (goal_env g) (goal_witness g) (* shouldn't really happen that we print a solved goal *)
    in
    let num = match maybe_num with
              | None -> ""
              | Some (i, n) -> BU.format2 " %s/%s" (string_of_int i) (string_of_int n)
    in
    let maybe_label =
        match g.label with
        | "" -> ""
        | l -> " (" ^ l ^ ")"
    in
    let actual_goal =
        if ps.tac_verb_dbg
        then goal_to_string_verbose g
        else BU.format3 "%s |- %s : %s\n" (Print.binders_to_string ", " g.goal_ctx_uvar.ctx_uvar_binders)
                                          w
                                          (tts (goal_env g) g.goal_ctx_uvar.ctx_uvar_typ)
    in
    BU.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal

let tacprint  (s:string)       = BU.print1 "TAC>> %s\n" s
let tacprint1 (s:string) x     = BU.print1 "TAC>> %s\n" (BU.format1 s x)
let tacprint2 (s:string) x y   = BU.print1 "TAC>> %s\n" (BU.format2 s x y)
let tacprint3 (s:string) x y z = BU.print1 "TAC>> %s\n" (BU.format3 s x y z)

let comp_to_typ (c:comp) : typ =
    match c.n with
    | Total (t, _)
    | GTotal (t, _) -> t
    | Comp ct -> ct.result_typ

let get_phi (g:goal) : option<term> =
    U.un_squash (N.unfold_whnf (goal_env g) (goal_type g))

let is_irrelevant (g:goal) : bool =
    Option.isSome (get_phi g)

let print (msg:string) : tac<unit> =
    tacprint msg;
    ret ()

let debugging () : tac<bool> =
    bind get (fun ps ->
    ret (Env.debug ps.main_context (Options.Other "Tac")))

(* Note: we use def ranges. In tactics we keep the position in there, while the
 * use range is the original position of the assertion / synth / splice. *)
let ps_to_string (msg, ps) =
    let p_imp imp =
        Print.uvar_to_string imp.imp_uvar.ctx_uvar_head
    in
    let n_active = List.length ps.goals in
    let n_smt    = List.length ps.smt_goals in
    let n = n_active + n_smt in
    String.concat ""
              ([format2 "State dump @ depth %s (%s):\n" (string_of_int ps.depth) msg;
                (if ps.entry_range <> Range.dummyRange
                 then format1 "Location: %s\n" (Range.string_of_def_range ps.entry_range)
                 else "");
                (if Env.debug ps.main_context (Options.Other "Imp")
                 then format1 "Imps: %s\n" (FStar.Common.string_of_list p_imp ps.all_implicits)
                 else "")]
                 @ (List.mapi (fun i g -> goal_to_string "Goal"     (Some (1 + i, n))            ps g) ps.goals)
                 @ (List.mapi (fun i g -> goal_to_string "SMT Goal" (Some (1 + n_active + i, n)) ps g) ps.smt_goals))

let goal_to_json g =
    let g_binders = Env.all_binders (goal_env g) |> Print.binders_to_json (Env.dsenv (goal_env g)) in
    JsonAssoc [("hyps", g_binders);
               ("goal", JsonAssoc [("witness", JsonStr (tts (goal_env g) (goal_witness g)));
                                   ("type", JsonStr (tts (goal_env g) (goal_type g)));
                                   ("label", JsonStr g.label)
                                  ])]

let ps_to_json (msg, ps) =
    JsonAssoc ([("label", JsonStr msg);
                ("depth", JsonInt ps.depth);
                ("goals", JsonList (List.map goal_to_json ps.goals));
                ("smt-goals", JsonList (List.map goal_to_json ps.smt_goals))] @
                (if ps.entry_range <> Range.dummyRange
                 then [("location", Range.json_of_def_range ps.entry_range)]
                 else []))

let dump_proofstate ps msg =
    Options.with_saved_options (fun () ->
        Options.set_option "print_effect_args" (Options.Bool true);
        print_generic "proof-state" ps_to_string ps_to_json (msg, ps))

let print_proof_state (msg:string) : tac<unit> =
    mk_tac (fun ps ->
                   let psc = ps.psc in
                   let subst = Cfg.psc_subst psc in
                   dump_proofstate (subst_proof_state subst ps) msg;
                   Success ((), ps))

let mlog f (cont : unit -> tac<'a>) : tac<'a> =
    bind get (fun ps -> log ps f; cont ())

let traise e =
    mk_tac (fun ps -> Failed (e, ps))

let fail (msg:string) =
    mk_tac (fun ps ->
        if Env.debug ps.main_context (Options.Other "TacFail")
        then dump_proofstate ps ("TACTIC FAILING: " ^ msg);
        Failed (TacticFailure msg, ps)
    )

let fail1 msg x     = fail (BU.format1 msg x)
let fail2 msg x y   = fail (BU.format2 msg x y)
let fail3 msg x y z = fail (BU.format3 msg x y z)
let fail4 msg x y z w = fail (BU.format4 msg x y z w)

let catch (t : tac<'a>) : tac<either<exn,'a>> =
    mk_tac (fun ps ->
            let tx = UF.new_transaction () in
            match run t ps with
            | Success (a, q) ->
                UF.commit tx;
                Success (Inr a, q)
            | Failed (m, q) ->
                UF.rollback tx;
                let ps = { ps with freshness = q.freshness } in //propagate the freshness even on failures
                Success (Inl m, ps)
           )

let recover (t : tac<'a>) : tac<either<exn,'a>> =
    mk_tac (fun ps ->
            match run t ps with
            | Success (a, q) -> Success (Inr a, q)
            | Failed (m, q)  -> Success (Inl m, q)
           )

let trytac (t : tac<'a>) : tac<option<'a>> =
    bind (catch t) (fun r ->
    match r with
    | Inr v -> ret (Some v)
    | Inl _ -> ret None)

let trytac_exn (t : tac<'a>) : tac<option<'a>> =
    mk_tac (fun ps ->
    try run (trytac t) ps
    with | Errors.Err (_, msg)
         | Errors.Error (_, msg, _) ->
           log ps (fun () -> BU.print1 "trytac_exn error: (%s)" msg);
           Success (None, ps))

let wrap_err (pref:string) (t : tac<'a>) : tac<'a> =
    mk_tac (fun ps ->
            match run t ps with
            | Success (a, q) ->
                Success (a, q)

            | Failed (TacticFailure msg, q) ->
                Failed (TacticFailure (pref ^ ": " ^ msg), q)

            | Failed (e, q) ->
                Failed (e, q)
           )

////////////////////////////////////////////////////////////////////
(* Some TRUSTED internal utilities *)

(* set : set the current proof state; shouldn't be exposed externally *)
let set (p:proofstate) : tac<unit> =
    mk_tac (fun _ -> Success ((), p))

let add_implicits (i:implicits) : tac<unit> =
    bind get (fun p ->
    set ({p with all_implicits=i@p.all_implicits}))

let __do_unify (env : env) (t1 : term) (t2 : term) : tac<bool> =
    let _ = if Env.debug env (Options.Other "1346") then
                  BU.print2 "%%%%%%%%do_unify %s =? %s\n"
                            (Print.term_to_string t1)
                            (Print.term_to_string t2) in
    try
        let res = Rel.teq_nosmt env t1 t2 in
        if Env.debug env (Options.Other "1346")
        then (BU.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                              (FStar.Common.string_of_option (Rel.guard_to_string env) res)
                              (Print.term_to_string t1)
                              (Print.term_to_string t2));
        match res with
        | None -> ret false
        | Some g ->
            bind (add_implicits g.implicits) (fun () ->
            ret true)
    with | Errors.Err (_, msg) -> begin
            mlog (fun () -> BU.print1 ">> do_unify error, (%s)\n" msg ) (fun _ ->
            ret false)
            end
         | Errors.Error (_, msg, r) -> begin
            mlog (fun () -> BU.print2 ">> do_unify error, (%s) at (%s)\n"
                                msg (Range.string_of_range r)) (fun _ ->
            ret false)
            end

let compress_implicits : tac<unit> =
    bind get (fun ps ->
    let imps = ps.all_implicits in
    let g = { Env.trivial_guard with implicits = imps } in
    let g = Rel.resolve_implicits_tac ps.main_context g in
    let ps' = { ps with all_implicits = g.implicits } in
    set ps')

let do_unify env t1 t2 : tac<bool> =
    bind idtac (fun () ->
    if Env.debug env (Options.Other "1346") then (
        Options.push ();
        let _ = Options.set_options Options.Set "--debug_level Rel --debug_level RelCheck" in
        ()
    );
    bind (__do_unify env t1 t2) (fun r ->
    if Env.debug env (Options.Other "1346") then
        Options.pop ();
    (* bind compress_implicits (fun _ -> *)
    ret r))

let remove_solved_goals : tac<unit> =
    bind get (fun ps ->
    let ps' = { ps with goals = List.filter (fun g -> Option.isNone (check_goal_solved g)) ps.goals } in
    set ps'
    )

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

let __dismiss : tac<unit> =
    bind get (fun p ->
    set ({p with goals=List.tl p.goals}))

let solve (goal : goal) (solution : term) : tac<unit> =
    let e = goal_env goal in
    mlog (fun () -> BU.print2 "solve %s := %s\n" (Print.term_to_string (goal_witness goal))
                                                 (Print.term_to_string solution)) (fun () ->
    bind (trysolve goal solution) (fun b ->
    if b
    then bind __dismiss (fun () -> remove_solved_goals)
    else fail (BU.format3 "%s does not solve %s : %s"
              (tts (goal_env goal) solution)
              (tts (goal_env goal) (goal_witness goal))
              (tts (goal_env goal) (goal_type goal)))))


let solve' (goal : goal) (solution : term) : tac<unit> =
    bind (set_solution goal solution) (fun () ->
    bind __dismiss (fun () ->
    remove_solved_goals))

(* These are UNTRUSTED! Goals don't really matter, implicits do. *)
let set_goals (gs:list<goal>) : tac<unit> =
    bind get (fun ps ->
    set ({ ps with goals = gs }))

let set_smt_goals (gs:list<goal>) : tac<unit> =
    bind get (fun ps ->
    set ({ ps with smt_goals = gs }))

let dismiss_all : tac<unit> = set_goals []

let nwarn = BU.mk_ref 0

let check_valid_goal g =
    if Options.defensive () then begin
        let b = true in
        let env = (goal_env g) in
        let b = b && Env.closed env (goal_witness g) in
        let b = b && Env.closed env (goal_type g) in
        let rec aux b e =
            match Env.pop_bv e with
            | None -> b
            | Some (bv, e) -> (
                let b = b && Env.closed e bv.sort in
                aux b e
                )
        in
        if not (aux b env) && !nwarn < 5
        then (Err.log_issue (goal_type g).pos
                  (Errors.Warning_IllFormedGoal, BU.format1 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                              (goal_to_string_verbose g));
              nwarn := !nwarn + 1)
    end

let add_goals (gs:list<goal>) : tac<unit> =
    bind get (fun p ->
    List.iter check_valid_goal gs;
    set ({p with goals=gs@p.goals}))

let add_smt_goals (gs:list<goal>) : tac<unit> =
    bind get (fun p ->
    List.iter check_valid_goal gs;
    set ({p with smt_goals=gs@p.smt_goals}))

let push_goals (gs:list<goal>) : tac<unit> =
    bind get (fun p ->
    List.iter check_valid_goal gs;
    set ({p with goals=p.goals@gs}))

let push_smt_goals (gs:list<goal>) : tac<unit> =
    bind get (fun p ->
    List.iter check_valid_goal gs;
    set ({p with smt_goals=p.smt_goals@gs}))

let replace_cur (g:goal) : tac<unit> =
    bind __dismiss (fun _ ->
    add_goals [g])

let new_uvar (reason:string) (env:env) (typ:typ) : tac<(term * ctx_uvar)> =
    //typ.pos should really never be a FStar.Range.range ... can it?
    let u, ctx_uvar, g_u = Env.new_implicit_var_aux reason typ.pos env typ Allow_untyped None in
    bind (add_implicits g_u.implicits) (fun _ ->
    ret (u, fst (List.hd ctx_uvar)))

//Any function that directly calls these utilities is also trusted
//End: Trusted utilities
////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////
(* Some utilities on goals *)
let is_true t =
    match U.un_squash t with
    | Some t' ->
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


let cur_goal () : tac<goal> =
    bind get (fun p ->
    match p.goals with
    | [] -> fail "No more goals (1)"
    | hd::tl ->
      match FStar.Syntax.Unionfind.find (hd.goal_ctx_uvar.ctx_uvar_head) with
      | None -> ret hd
      | Some t ->
        BU.print2 "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                (goal_to_string_verbose hd)
                (Print.term_to_string t);
        ret hd)

let tadmit_t (t:term) : tac<unit> = wrap_err "tadmit_t" <|
    bind get (fun ps ->
    bind (cur_goal ()) (fun g ->
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

let mk_irrelevant_goal (reason:string) (env:env) (phi:typ) opts label : tac<goal> =
    let typ = U.mk_squash (env.universe_of env phi) phi in
    bind (new_uvar reason env typ) (fun (_, ctx_uvar) ->
    let goal = mk_goal env ctx_uvar opts false label in
    ret goal)

(* Annoying duplication here *)
let __tc (e : env) (t : term) : tac<(term * typ * guard_t)> =
    bind get (fun ps ->
    mlog (fun () -> BU.print1 "Tac> __tc(%s)\n" (Print.term_to_string t)) (fun () ->
    let e = {e with uvar_subtyping=false} in
    try ret (TcTerm.type_of_tot_term e t)
    with | Errors.Err (_, msg)
         | Errors.Error (_, msg, _) -> begin
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
    with | Errors.Err (_, msg)
         | Errors.Error (_, msg, _) -> begin
           fail3 "Cannot type %s in context (%s). Error = (%s)" (tts e t)
                                                  (Env.all_binders e |> Print.binders_to_string ", ")
                                                  msg
           end))

let __tc_lax (e : env) (t : term) : tac<(term * typ * guard_t)> =
    bind get (fun ps ->
    mlog (fun () -> BU.print1 "Tac> __tc(%s)\n" (Print.term_to_string t)) (fun () ->
    let e = {e with uvar_subtyping=false} in
    let e = {e with lax = true} in
    try let t, lc, g = TcTerm.tc_term e t in
        ret (t, lc.res_typ, g)
    with | Errors.Err (_, msg)
         | Errors.Error (_, msg, _) -> begin
           fail3 "Cannot type %s in context (%s). Error = (%s)" (tts e t)
                                                  (Env.all_binders e |> Print.binders_to_string ", ")
                                                  msg
           end))

let istrivial (e:env) (t:term) : bool =
    let steps = [Env.Reify; Env.UnfoldUntil delta_constant; Env.Primops; Env.Simplify; Env.UnfoldTac; Env.Unmeta] in
    let t = normalize steps e t in
    is_true t

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

let getopts : tac<FStar.Options.optionstate> =
    bind (trytac (cur_goal ())) (function
    | Some g -> ret g.opts
    | None -> ret (FStar.Options.peek ()))

let proc_guard (reason:string) (e : env) (g : guard_t) : tac<unit> =
    mlog (fun () ->
        BU.print2 "Processing guard (%s:%s)\n" reason (Rel.guard_to_string e g)) (fun () ->
    bind (add_implicits g.implicits) (fun () ->
    bind getopts (fun opts ->
    match (Rel.simplify_guard e g).guard_f with
    | TcComm.Trivial -> ret ()
    | TcComm.NonTrivial f ->
        if istrivial e f // trivializes further...
        then ret ()
        else // check the policy
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
        bind (mk_irrelevant_goal reason e f opts "") (fun goal ->
        let goal = { goal with is_guard = true } in
        push_goals [goal]))

    | SMT ->
        mlog (fun () -> BU.print2 "Sending guard (%s:%s) to SMT goal\n" reason (Rel.guard_to_string e g)) (fun () ->
        bind (mk_irrelevant_goal reason e f opts "") (fun goal ->
        let goal = { goal with is_guard = true } in
        push_smt_goals [goal]))

    | Force ->
        mlog (fun () -> BU.print2 "Forcing guard (%s:%s)\n" reason (Rel.guard_to_string e g)) (fun () ->
        try if not (Env.is_trivial <| Rel.discharge_guard_no_smt e g)
            then
                mlog (fun () -> BU.print1 "guard = %s\n" (Rel.guard_to_string e g)) (fun () ->
                fail1 "Forcing the guard failed (%s)" reason)
            else ret ()
        with
        | _ -> mlog (fun () -> BU.print1 "guard = %s\n" (Rel.guard_to_string e g)) (fun () ->
               fail1 "Forcing the guard failed (%s)" reason))))))

let tc (t : term) : tac<typ> = wrap_err "tc" <|
    bind (cur_goal ()) (fun goal ->
    bind (__tc_lax (goal_env goal) t) (fun (_, typ, _) ->
    (* Why lax? What about the guard? It doesn't matter! tc is only
     * a way for metaprograms to query the typechecker, but
     * the result has no effect on the proofstate and nor is it
     * taken for a fact that the typing is correct. *)
    ret typ
    ))

let add_irrelevant_goal reason env phi opts label : tac<unit> =
    bind (mk_irrelevant_goal reason env phi opts label) (fun goal ->
    add_goals [goal])

let trivial () : tac<unit> =
    bind (cur_goal ()) (fun goal ->
    if istrivial (goal_env goal) (goal_type goal)
    then solve' goal U.exp_unit
    else fail1 "Not a trivial goal: %s" (tts (goal_env goal) (goal_type goal))
    )

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
    bind (cur_goal ()) (fun goal ->
    match U.arrow_one (goal_type goal) with
    | Some (b, c) ->
        if not (U.is_total_comp c)
        then fail "Codomain is effectful"
        else let env' = Env.push_binders (goal_env goal) [b] in
             let typ' = comp_to_typ c in
             //BU.print1 "[intro]: current goal is %s" (goal_to_string goal);
             //BU.print1 "[intro]: current goal witness is %s" (Print.term_to_string (goal_witness goal));
             //BU.print1 "[intro]: with goal type %s" (Print.term_to_string (goal_type goal));
             //BU.print2 "[intro]: with binder = %s, new goal = %s"
             //         (Print.binders_to_string ", " [b])
             //         (Print.term_to_string typ');
             bind (new_uvar "intro" env' typ') (fun (body, ctx_uvar) ->
             let sol = U.abs [b] body (Some (U.residual_comp_of_comp c)) in
             //BU.print1 "[intro]: solution is %s"
             //           (Print.term_to_string sol);
             //BU.print1 "[intro]: old goal is %s" (goal_to_string goal);
             //BU.print1 "[intro]: new goal is %s"
             //           (Print.ctx_uvar_to_string ctx_uvar);
             //ignore (FStar.Options.set_options Options.Set "--debug_level Rel");
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
    bind (cur_goal ()) (fun goal ->
    BU.print_string "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
    BU.print_string "WARNING (intro_rec): proceed at your own risk...\n";
    match U.arrow_one (goal_type goal) with
    | Some (b, c) ->
        if not (U.is_total_comp c)
        then fail "Codomain is effectful"
        else let bv = gen_bv "__recf" None (goal_type goal) in
             let bs = [S.mk_binder bv; b] in // recursively bound name and argument we're introducing
             let env' = Env.push_binders (goal_env goal) bs in
             bind (new_uvar "intro_rec" env' (comp_to_typ c)) (fun (u, ctx_uvar_u) ->
             let lb = U.mk_letbinding (Inl bv) [] (goal_type goal) PC.effect_Tot_lid (U.abs [b] u None) [] Range.dummyRange in
             let body = S.bv_to_name bv in
             let lbs, body = SS.close_let_rec [lb] body in
             let tm = mk (Tm_let ((true, lbs), body)) None (goal_witness goal).pos in
             bind (set_solution goal tm) (fun () ->
             bind (replace_cur (bnorm_goal ({ goal with goal_ctx_uvar=ctx_uvar_u}))) (fun _ ->
             ret (S.mk_binder bv, b))))
    | None ->
        fail1 "intro_rec: goal is not an arrow (%s)" (tts (goal_env goal) (goal_type goal))
    )

let norm (s : list<EMB.norm_step>) : tac<unit> =
    bind (cur_goal ()) (fun goal ->
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
    bind (cur_goal ()) (fun g ->
    match Rel.base_and_refinement (goal_env g) (goal_type g) with
    | _, None -> fail "not a refinement"
    | t, Some (bv, phi) ->
        let g1 = goal_with_type g t in
        let bv, phi = match SS.open_term [S.mk_binder bv] phi with
                      | bvs, phi -> fst (List.hd bvs), phi
        in
        bind (mk_irrelevant_goal "refine_intro refinement" (goal_env g)
                    (SS.subst [S.NT (bv, (goal_witness g))] phi) g.opts g.label) (fun g2 ->
        bind __dismiss (fun _ ->
        add_goals [g1;g2])))

let __exact_now set_expected_typ (t:term) : tac<unit> =
    bind (cur_goal ()) (fun goal ->
    let env = if set_expected_typ
              then Env.set_expected_typ (goal_env goal) (goal_type goal)
              else (goal_env goal)
    in
    bind (__tc env t) (fun (t, typ, guard) ->
    mlog (fun () -> BU.print2 "__exact_now: got type %s\n__exact_now: and guard %s\n"
                                                     (Print.term_to_string typ)
                                                     (Rel.guard_to_string (goal_env goal) guard)) (fun _ ->
    bind (proc_guard "__exact typing" (goal_env goal) guard) (fun _ ->
    mlog (fun () -> BU.print2 "__exact_now: unifying %s and %s\n" (Print.term_to_string typ)
                                                                  (Print.term_to_string (goal_type goal))) (fun _ ->
    bind (do_unify (goal_env goal) typ (goal_type goal)) (fun b -> if b
    then solve goal t
    else fail4 "%s : %s does not exactly solve the goal %s (witness = %s)"
                    (tts (goal_env goal) t)
                    (tts (goal_env goal) typ)
                    (tts (goal_env goal) (goal_type goal))
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

let rec mapM (f : 'a -> tac<'b>) (l : list<'a>) : tac<list<'b>> =
    match l with
    | [] -> ret []
    | x::xs ->
        bind (f x) (fun y ->
        bind (mapM f xs) (fun ys ->
        ret (y::ys)))

let rec  __try_match_by_application (acc : list<(term * aqual * ctx_uvar)>)
                                    (e : env) (ty1 : term) (ty2 : term)
                                        : tac<list<(term * aqual * ctx_uvar)>> =
    bind (do_unify e ty1 ty2) (function
    | true ->
        (* Done! *)
        ret acc
    | false -> begin
        (* Not a match, try instantiating the first type by application *)
        match U.arrow_one ty1 with
        | None ->
            fail2 "Could not instantiate, %s to %s" (Print.term_to_string ty1) (Print.term_to_string ty2)
        | Some (b, c) ->
            if not (U.is_total_comp c) then fail "Codomain is effectful" else
            bind (new_uvar "apply arg" e (fst b).sort) (fun (uvt, uv) ->
            let typ = comp_to_typ c in
            let typ' = SS.subst [S.NT (fst b, uvt)] typ in
            __try_match_by_application ((uvt, snd b, uv)::acc) e typ' ty2)
    end)

(* Can t1 match t2 if it's applied to arguments? If so return uvars for them *)
(* NB: Result is reversed, which helps so we use fold_right instead of fold_left *)
let try_match_by_application (e : env) (ty1 : term) (ty2 : term) : tac<list<(term * aqual * ctx_uvar)>> =
    __try_match_by_application [] e ty1 ty2

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
let t_apply (uopt:bool) (tm:term) : tac<unit> = wrap_err "apply" <|
    mlog (fun () -> BU.print1 "t_apply: tm = %s\n" (Print.term_to_string tm)) (fun _ ->
    bind (cur_goal ()) (fun goal ->
    let e = goal_env goal in
    bind (__tc e tm) (fun (tm, typ, guard) ->
    // Focus helps keep the goal order
    let typ = bnorm e typ in
    bind (try_match_by_application e typ (goal_type goal)) (fun uvs ->
    (* use normal implicit application for meta-args: meta application does
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
    proc_guard "apply guard" e guard
    ))))))

// returns pre and post
let lemma_or_sq (c : comp) : option<(term * term)> =
    let ct = U.comp_to_comp_typ_nouniv c in
    if lid_equals ct.effect_name PC.effect_Lemma_lid then
        let pre, post = match ct.effect_args with
                        | pre::post::_ -> fst pre, fst post
                        | _ -> failwith "apply_lemma: impossible: not a lemma"
        in
        // Lemma post is thunked, and is specialized to U_zero
        let post = U.mk_app post [S.as_arg U.exp_unit] in
        Some (pre, post)
    else if U.is_pure_effect ct.effect_name then
        map_opt (U.un_squash ct.result_typ) (fun post -> (U.t_true, post))
    else
        None

let rec fold_left (f : ('a -> 'b -> tac<'b>)) (e : 'b) (xs : list<'a>) : tac<'b> =
    match xs with
    | [] -> ret e
    | x::xs -> bind (f x e) (fun e' -> fold_left f e' xs)

let apply_lemma (tm:term) : tac<unit> = wrap_err "apply_lemma" <| focus (
    bind get (fun ps ->
    mlog (fun () -> BU.print1 "apply_lemma: tm = %s\n" (Print.term_to_string tm)) (fun _ ->
    let is_unit_t t = match (SS.compress t).n with
    | Tm_fvar fv when S.fv_eq_lid fv PC.unit_lid -> true
    | _ -> false
    in
    bind (cur_goal ()) (fun goal ->
    bind (__tc (goal_env goal) tm) (fun (tm, t, guard) ->
    let bs, comp = U.arrow_formals_comp t in
    match lemma_or_sq comp with
    | None -> fail "not a lemma or squashed function"
    | Some (pre, post) ->
    bind (
       fold_left (fun (b, aq) (uvs, imps, subst) ->
               let b_t = SS.subst subst b.sort in
               if is_unit_t b_t
               then
                   // Simplification: if the argument is simply unit, then don't ask for it
                   ret <| ((U.exp_unit, aq)::uvs, imps, S.NT(b, U.exp_unit)::subst)
               else
                   bind (new_uvar "apply_lemma" (goal_env goal) b_t) (fun (t, u) ->
                   ret <| ((t, aq)::uvs, (t, u)::imps, S.NT(b, t)::subst))
               )
       ([], [], [])
       bs)
    (fun (uvs, implicits, subst) ->
    let implicits = List.rev implicits in
    let uvs = List.rev uvs in
    let pre  = SS.subst subst pre in
    let post = SS.subst subst post in
    bind (do_unify (goal_env goal) (U.mk_squash U_zero post) (goal_type goal)) (fun b ->
    if not b
    then fail3 "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                            (tts (goal_env goal) tm)
                            (tts (goal_env goal) (U.mk_squash U_zero post))
                            (tts (goal_env goal) (goal_type goal))
    else
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
            let t1 = BU.now () in
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
                let env = {(goal_env goal) with gamma=ctx_uvar.ctx_uvar_gamma} in
                let g_typ =
                  // NS:01/24: use the fast path instead, knowing that term is at least well-typed
                  // NS:05/25: protecting it under this option,
                  //           since it causes a regression in examples/vale/*Math_i.fst
                  // GM: Made it the default, but setting must_total to true
                  FStar.TypeChecker.TcTerm.check_type_of_well_typed_term' true env term ctx_uvar.ctx_uvar_typ
                in
                bind (proc_guard
                       (if ps.tac_verb_dbg
                        then BU.format2 "apply_lemma solved arg %s to %s\n" (Print.ctx_uvar_to_string ctx_uvar)
                                                                            (Print.term_to_string term)
                        else "apply_lemma solved arg")
                        (goal_env goal) g_typ) (fun () ->
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
        bind (proc_guard "apply_lemma guard" (goal_env goal) guard) (fun _ ->
        bind (if not (istrivial (goal_env goal) (U.mk_squash U_zero pre)) //lemma preconditions are in U_zero
              then add_irrelevant_goal "apply_lemma precondition" (goal_env goal) pre goal.opts goal.label
              else ret ()) (fun _ ->
        add_goals sub_goals))))
    )))))))

let destruct_eq' (typ : typ) : option<(term * term)> =
    match U.destruct_typ_as_formula typ with
    | Some (U.BaseConn(l, [_; (e1, _); (e2, _)]))
      when Ident.lid_equals l PC.eq2_lid
      ||    Ident.lid_equals l PC.c_eq2_lid ->
        Some (e1, e2)
    | _ ->
        None

let destruct_eq (typ : typ) : option<(term * term)> =
    match destruct_eq' typ with
    | Some t -> Some t
    | None ->
        // Retry for a squashed one
        begin match U.un_squash typ with
        | Some typ -> destruct_eq' typ
        | None -> None
        end

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

let subst_goal (b1 : bv) (b2 : bv) (s:list<subst_elt>) (g:goal) : option<goal> =
    map_opt (split_env b1 (goal_env g)) (fun (e0, b1, bvs) ->
        let s1 bv = { bv with sort = SS.subst s bv.sort } in
        let bvs = List.map s1 bvs in
        let new_env = push_bvs e0 (b2::bvs) in
        let new_goal = {
            g.goal_ctx_uvar with
                ctx_uvar_gamma=new_env.gamma;
                ctx_uvar_binders=Env.all_binders new_env;
                ctx_uvar_typ = SS.subst s (goal_type g);
        } in
        { g with goal_ctx_uvar=new_goal }
    )

let rewrite (h:binder) : tac<unit> = wrap_err "rewrite" <|
    bind (cur_goal ()) (fun goal ->
    let bv, _ = h in
    mlog (fun _ -> BU.print2 "+++Rewrite %s : %s\n" (Print.bv_to_string bv) (Print.term_to_string bv.sort)) (fun _ ->
    match split_env bv (goal_env goal) with
    | None -> fail "binder not found in environment"
    | Some (e0, bv, bvs) -> begin
        match destruct_eq bv.sort with
        | Some (x, e) ->
        (match (SS.compress x).n with
           | Tm_name x ->
             let s = [NT(x,e)] in
             let s1 bv = { bv with sort = SS.subst s bv.sort } in
             let bvs = List.map s1 bvs in
             let new_env = push_bvs e0 (bv::bvs) in
             let new_goal = {
                 goal.goal_ctx_uvar with
                     ctx_uvar_gamma=new_env.gamma;
                     ctx_uvar_binders=Env.all_binders new_env;
                     ctx_uvar_typ = SS.subst s (goal_type goal);
             } in
             replace_cur ({goal with goal_ctx_uvar=new_goal})
           | _ ->
             fail "Not an equality hypothesis with a variable on the LHS")
        | _ -> fail "Not an equality hypothesis"
        end))

let rename_to (b : binder) (s : string) : tac<unit> = wrap_err "rename_to" <|
    bind (cur_goal ()) (fun goal ->
    let bv, _ = b in
    let bv' = freshen_bv ({ bv with ppname = mk_ident (s, bv.ppname.idRange) }) in
    let s = [NT (bv, S.bv_to_name bv')] in
    match subst_goal bv bv' s goal with
    | None -> fail "binder not found in environment"
    | Some goal -> replace_cur goal)

let binder_retype (b : binder) : tac<unit> = wrap_err "binder_retype" <|
    bind (cur_goal ()) (fun goal ->
    let bv, _ = b in
    match split_env bv (goal_env goal) with
    | None -> fail "binder is not present in environment"
    | Some (e0, bv, bvs) ->
        let (ty, u) = U.type_u () in
        bind (new_uvar "binder_retype" e0 ty) (fun (t', u_t') ->
        //NS: Question ... u_t' is dropped; why?
        //GM: No need for it... we just use t' which is approx (Tm_uvar u_t').
        //    The uvar is tracked in the proofstate too.
        let bv'' = {bv with sort = t'} in
        let s = [S.NT (bv, S.bv_to_name bv'')] in
        let bvs = List.map (fun b -> { b with sort = SS.subst s b.sort }) bvs in
        let env' = push_bvs e0 (bv''::bvs) in
        bind __dismiss (fun _ ->
        let new_goal =
            goal_with_type
                (goal_with_env goal env')
                (SS.subst s (goal_type goal))
        in
        bind (add_goals [new_goal]) (fun _ ->
              add_irrelevant_goal "binder_retype equation" e0
                  (U.mk_eq2 (U_succ u) ty bv.sort t') goal.opts goal.label)))
    )

(* TODO: move to bv *)
let norm_binder_type (s : list<EMB.norm_step>) (b : binder) : tac<unit> = wrap_err "norm_binder_type" <|
    bind (cur_goal ()) (fun goal ->
    let bv, _ = b in
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
    bind (cur_goal ()) (fun goal ->
    match Env.pop_bv (goal_env goal) with
    | None -> fail "Cannot revert; empty context"
    | Some (x, env') ->
        let typ' = U.arrow [(x, None)] (mk_Total (goal_type goal)) in
        bind (new_uvar "revert" env' typ') (fun (r, u_r) ->
        bind (set_solution goal (S.mk_Tm_app r [S.as_arg (S.bv_to_name x)] None (goal_type goal).pos)) (fun () ->
        let g = mk_goal env' u_r goal.opts goal.is_guard goal.label in
        replace_cur g)))

let free_in bv t =
    Util.set_mem bv (SF.names t)

let rec clear (b : binder) : tac<unit> =
    let bv = fst b in
    bind (cur_goal ()) (fun goal ->
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
        bind (new_uvar "clear.witness" env' (goal_type goal)) (fun (ut, uvar_ut) ->
        bind (set_solution goal ut) (fun () ->
        replace_cur (mk_goal env' uvar_ut goal.opts goal.is_guard goal.label))))))

let clear_top () : tac<unit> =
    bind (cur_goal ()) (fun goal ->
    match Env.pop_bv (goal_env goal) with
    | None -> fail "Cannot clear; empty context"
    | Some (x, _) -> clear (S.mk_binder x)) // we ignore the qualifier anyway

let prune (s:string) : tac<unit> =
    bind (cur_goal ()) (fun g ->
    let ctx = goal_env g in
    let ctx' = Env.rem_proof_ns ctx (path_of_text s) in
    let g' = goal_with_env g ctx' in
    bind __dismiss (fun _ -> add_goals [g']))

let addns (s:string) : tac<unit> =
    bind (cur_goal ()) (fun g ->
    let ctx = goal_env g in
    let ctx' = Env.add_proof_ns ctx (path_of_text s) in
    let g' = goal_with_env g ctx' in
    bind __dismiss (fun _ -> add_goals [g']))

let rec tac_fold_env (d : direction) (f : env -> term -> tac<term>) (env : env) (t : term) : tac<term> =
    let tn = (SS.compress t).n in
    bind (if d = TopDown
          then f env ({ t with n = tn })
          else ret t) (fun t ->
    let ff = tac_fold_env d f env in
    let tn = match (SS.compress t).n with
             | Tm_app (hd, args) ->
                  bind (ff hd) (fun hd ->
                  let fa (a,q) = bind (ff a) (fun a -> (ret (a,q))) in
                  bind (mapM fa args) (fun args ->
                  ret (Tm_app (hd, args))))

             | Tm_abs (bs, t, k) ->
                 let bs, t' = SS.open_term bs t in
                 bind (tac_fold_env d f (Env.push_binders env bs) t') (fun t'' ->
                 ret (Tm_abs (SS.close_binders bs, SS.close bs t'', k)))

             | Tm_arrow (bs, k) -> ret tn //TODO: do we care?

             | Tm_match (hd, brs) ->
                 bind (ff hd) (fun hd ->
                 let ffb br =
                    let (pat, w, e) = SS.open_branch br in
                    let bvs = S.pat_bvs pat in
                    let ff = tac_fold_env d f (Env.push_bvs env bvs) in
                    bind (ff e) (fun e ->
                    let br = SS.close_branch (pat, w, e) in
                    ret br)
                 in
                 bind (mapM ffb brs) (fun brs ->
                 ret (Tm_match (hd, brs))))

             | Tm_let ((false, [{ lbname = Inl bv; lbdef = def }]), e) ->
                (* ugh *)
                let lb = match (SS.compress t).n with
                         | Tm_let ((false, [lb]), _) -> lb
                         | _ -> failwith "impossible"
                in
                let fflb lb =
                    bind (ff lb.lbdef) (fun def ->
                    ret ({lb with lbdef = def }))
                in
                bind (fflb lb) (fun lb ->
                let bs, e = SS.open_term [S.mk_binder bv] e in
                let ff = tac_fold_env d f (Env.push_binders env bs) in
                bind (ff e) (fun e ->
                let e = SS.close bs e in
                ret (Tm_let ((false, [lb]), e))))


             | Tm_let ((true, lbs), e) ->
                let fflb lb =
                    bind (ff lb.lbdef) (fun def ->
                    ret ({lb with lbdef = def }))
                in
                let lbs, e = SS.open_let_rec lbs e in
                bind (mapM fflb lbs) (fun lbs ->
                bind (ff e) (fun e ->
                let lbs, e = SS.close_let_rec lbs e in
                ret (Tm_let ((true, lbs), e))))

             | Tm_ascribed (t, asc, eff) ->
                bind (ff t) (fun t -> ret (Tm_ascribed (t, asc, eff)))

             | Tm_meta (t, m) ->
                bind (ff t) (fun t -> ret (Tm_meta (t, m)))

             | _ ->
                ret tn
    in
    bind tn (fun tn ->
    let t' = { t with n = tn } in
    if d = BottomUp
    then f env t'
    else ret t'))

(*
 * Allows for replacement of individual subterms in the goal, asking the user to provide
 * a proof of the equality. Users are presented with goals of the form `t == ?u` for `t`
 * subterms of the current goal and `?u` a fresh unification variable. The users then
 * calls apply_lemma to fully instantiate `u` and provide a proof of the equality.
 * If all that is successful, the term is rewritten.
 *)
let pointwise_rec (ps : proofstate) (tau : tac<unit>) opts label (env : Env.env) (t : term) : tac<term> =
    let t, lcomp, g = TcTerm.tc_term ({ env with lax = true }) t in
    if not (U.is_pure_or_ghost_lcomp lcomp) || not (Env.is_trivial g) then
        ret t // Don't do anything for possibly impure terms
    else
        let rewrite_eq =
          let typ = lcomp.res_typ in
          bind (new_uvar "pointwise_rec" env typ) (fun (ut, uvar_ut) -> //NS: FIXME uvar_ut dropped?
          log ps
             (fun () ->
                  BU.print2 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                            (Print.term_to_string t)
                            (Print.term_to_string ut));
          bind (add_irrelevant_goal "pointwise_rec equation" env
                                    (U.mk_eq2 (TcTerm.universe_of env typ) typ t ut) opts label) (fun _ ->
          focus (
                bind tau (fun _ ->
                // Try to get rid  of all the unification lambdas
                let ut = N.reduce_uvar_solutions env ut in
                log ps (fun () ->
                    BU.print2 "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                (Print.term_to_string t)
                                (Print.term_to_string ut));
                ret ut))
          ))
       in
       bind (catch rewrite_eq) (fun x ->
       match x with
       // TODO: Share a `Skip` exception to userspace
       | Inl (TacticFailure "SKIP") -> ret t
       | Inl e -> traise e
       | Inr x -> ret x)

(*
 * Allows for replacement of individual subterms in the goal, asking the user to provide
 * a proof of the equality. Users are presented with goals of the form `t == ?u` for `t`
 * subterms of the current goal and `?u` a fresh unification variable. The users then
 * calls apply_lemma to fully instantiate `u` and provide a proof of the equality.
 * If all that is successful, the term is rewritten.
 *)
type ctrl = FStar.BigInt.t
let keepGoing : ctrl = FStar.BigInt.zero
let proceedToNextSubtree = FStar.BigInt.one
let globalStop = FStar.BigInt.succ_big_int FStar.BigInt.one
type rewrite_result = bool
let skipThisTerm = false
let rewroteThisTerm = true

type ctrl_tac<'a> = tac<('a * ctrl)>
let rec ctrl_tac_fold
        (f : env -> term -> ctrl_tac<term>)
        (env:env)
        (ctrl:ctrl)
        (t : term) : ctrl_tac<term> =
    let keep_going c =
        if c = proceedToNextSubtree then keepGoing
        else c
    in
    let maybe_continue ctrl t k =
        if ctrl = globalStop then ret (t, globalStop)
        else if ctrl = proceedToNextSubtree then ret (t, keepGoing)
        else k t
    in
    maybe_continue ctrl (SS.compress t) (fun t ->
    bind (f env ({ t with n = t.n }))   (fun (t, ctrl) ->
    maybe_continue ctrl t (fun t ->
    match (SS.compress t).n with
    | Tm_app (hd, args) ->
        bind (ctrl_tac_fold f env ctrl hd) (fun (hd, ctrl) ->
        let ctrl = keep_going ctrl in
        bind (ctrl_tac_fold_args f env ctrl args) (fun (args, ctrl) ->
        ret ({t with n=Tm_app (hd, args)}, ctrl)))
    | Tm_abs (bs, t, k) ->
        let bs, t' = SS.open_term bs t in
        bind (ctrl_tac_fold f (Env.push_binders env bs) ctrl t') (fun (t'', ctrl) ->
        ret ({t with n=Tm_abs (SS.close_binders bs, SS.close bs t'', k)}, ctrl))
    | Tm_arrow (bs, k) ->
        ret (t, ctrl) //TODO
    | _ ->
        ret (t, ctrl))))

and ctrl_tac_fold_args
        (f : env -> term -> ctrl_tac<term>)
        (env:env)
        (ctrl:ctrl)
        (ts : list<arg>) : ctrl_tac<(list<arg>)> =
    match ts with
    | [] -> ret ([], ctrl)
    | (t, q)::ts ->
      bind (ctrl_tac_fold f env ctrl t) (fun (t, ctrl) ->
      bind (ctrl_tac_fold_args f env ctrl ts) (fun (ts, ctrl) ->
      ret ((t,q)::ts, ctrl)))

let rewrite_rec (ps : proofstate)
                (ctrl:term -> ctrl_tac<rewrite_result>)
                (rewriter: tac<unit>)
                opts label
                (env : Env.env)
                (t : term) : ctrl_tac<term> =
    let t = SS.compress t in
    (* GM: We should improve this bit, making a goal is not very cheap
     * since the implicits must be kept in track and checked. Running with
     * 0 goals is possible, but some tactics that depend on an environment,
     * such as `norm_term`, will fail. *)
    bind (bind (add_irrelevant_goal "dummy"
                    env
                    U.t_true
                    opts
                    label) (fun _ ->
          bind (ctrl t) (fun res ->
          bind (trivial ()) (fun _ ->
          ret res)))) (fun (should_rewrite, ctrl) ->
    if not should_rewrite
    then ret (t, ctrl)
    else let t, lcomp, g = TcTerm.tc_term ({ env with lax = true }) t in //re-typechecking the goal is expensive
         if not (U.is_pure_or_ghost_lcomp lcomp) || not (Env.is_trivial g) then
           ret (t, globalStop) // Don't do anything for possibly impure terms
         else
           let typ = lcomp.res_typ in
           bind (new_uvar "pointwise_rec" env typ) (fun (ut, uvar_ut) -> //NS: FIXME uvar_ut dropped?
           log ps (fun () ->
              BU.print2 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                (Print.term_to_string t) (Print.term_to_string ut));
           bind (add_irrelevant_goal
                             "rewrite_rec equation"
                             env
                             (U.mk_eq2 (TcTerm.universe_of env typ) typ t ut)
                             opts
                             label) (fun _ ->
           focus
            (bind rewriter (fun _ ->
             // Try to get rid of all the unification lambdas
             let ut = N.reduce_uvar_solutions env ut in
             log ps (fun () ->
                BU.print2 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                            (Print.term_to_string t)
                            (Print.term_to_string ut));
             ret (ut, ctrl))))))

let topdown_rewrite (ctrl:term -> ctrl_tac<rewrite_result>)
                    (rewriter:tac<unit>) : tac<unit> = wrap_err "topdown_rewrite" <|
    bind get (fun ps ->
    let g, gs = match ps.goals with
                | g::gs -> g, gs
                | [] -> failwith "no goals"
    in
    let gt = (goal_type g) in
    log ps (fun () ->
        BU.print1 "Topdown_rewrite starting with %s\n" (Print.term_to_string gt));
    bind dismiss_all (fun _ ->
    bind (ctrl_tac_fold (rewrite_rec ps ctrl rewriter g.opts g.label) (goal_env g) keepGoing gt) (fun (gt', _) ->
    log ps (fun () ->
        BU.print1 "Topdown_rewrite seems to have succeded with %s\n" (Print.term_to_string gt'));
    bind (push_goals gs) (fun _ ->
    add_goals [goal_with_type g gt']))))


let pointwise (d : direction) (tau:tac<unit>) : tac<unit> = wrap_err "pointwise" <|
    bind get (fun ps ->
    let g, gs = match ps.goals with
                | g::gs -> g, gs
                | [] -> failwith "no goals"
    in
    let gt = (goal_type g) in
    log ps (fun () ->
        BU.print1 "Pointwise starting with %s\n" (Print.term_to_string gt));
    bind dismiss_all (fun _ ->
    bind (tac_fold_env d (pointwise_rec ps tau g.opts g.label) (goal_env g) gt) (fun gt' ->
    log ps (fun () ->
        BU.print1 "Pointwise seems to have succeded with %s\n" (Print.term_to_string gt'));
    bind (push_goals gs) (fun _ ->
    add_goals [goal_with_type g gt']))))

let trefl () : tac<unit> = wrap_err "trefl" <|
    bind (cur_goal ()) (fun g ->
    match U.un_squash (goal_type g) with
    | Some t ->
        begin
        let hd, args = U.head_and_args' t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [_; (l, _); (r, _)] when S.fv_eq_lid fv PC.eq2_lid ->
            bind (do_unify (goal_env g) l r) (fun b ->
            if b
            then solve' g U.exp_unit
            else
            let l = N.normalize [Env.UnfoldUntil delta_constant; Env.Primops; Env.UnfoldTac] (goal_env g) l in
            let r = N.normalize [Env.UnfoldUntil delta_constant; Env.Primops; Env.UnfoldTac] (goal_env g) r in
            bind (do_unify (goal_env g) l r) (fun b ->
            if b
            then solve' g U.exp_unit
            else
            fail2 "not a trivial equality ((%s) vs (%s))" (tts (goal_env g) l) (tts (goal_env g) r)))
        | hd, _ ->
            fail1 "trefl: not an equality (%s)" (tts (goal_env g) t)
        end
     | None ->
        fail "not an irrelevant goal")

let dup () : tac<unit> =
    bind (cur_goal ()) (fun g ->
    bind (new_uvar "dup" (goal_env g) (goal_type g)) (fun (u, u_uvar) ->
    let g' = { g with goal_ctx_uvar = u_uvar } in
    bind __dismiss (fun _ ->
    bind (add_irrelevant_goal "dup equation" (goal_env g)
               (U.mk_eq2 (TcTerm.universe_of (goal_env g) (goal_type g)) (goal_type g) u (goal_witness g)) g.opts g.label) (fun _ ->
    bind (add_goals [g']) (fun _ ->
    ret ())))))

// longest_prefix f l1 l2 = (p, r1, r2) ==> l1 = p@r1 /\ l2 = p@r2
let rec longest_prefix (f : 'a -> 'a -> bool) (l1 : list<'a>) (l2 : list<'a>) : list<'a> * list<'a> * list<'a> =
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
        List.fold_right (fun b f -> U.mk_forall_no_univ (fst b) f) bs f
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
    bind (mk_irrelevant_goal "joined" nenv ng g1.opts g1.label) (fun goal ->
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

(* TODO: special case of destruct? But `bool` is not an inductive.. *)
let cases (t : term) : tac<(term * term)> = wrap_err "cases" <|
    bind (cur_goal ()) (fun g ->
    bind (__tc (goal_env g) t) (fun (t, typ, guard) ->
    let hd, args = U.head_and_args typ in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [(p, _); (q, _)] when S.fv_eq_lid fv PC.or_lid ->
        let v_p = S.new_bv None p in
        let v_q = S.new_bv None q in
        let g1 = goal_with_env g (Env.push_bv (goal_env g) v_p) in
        let g2 = goal_with_env g (Env.push_bv (goal_env g) v_q) in
        bind __dismiss (fun _ ->
        bind (add_goals [g1; g2]) (fun _ ->
        ret (S.bv_to_name v_p, S.bv_to_name v_q)))
    | _ ->
        fail1 "Not a disjunction: %s" (tts (goal_env g) typ)))

let set_options (s : string) : tac<unit> = wrap_err "set_options" <|
    bind (cur_goal ()) (fun g ->
    FStar.Options.push ();
    FStar.Options.set (Util.smap_copy g.opts); // copy the map, they are not purely functional
    let res = FStar.Options.set_options FStar.Options.Set s in
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
    bind (cur_goal ()) (fun g ->
    ret (Options.lax () || (goal_env g).lax))

let unquote (ty : term) (tm : term) : tac<term> = wrap_err "unquote" <|
    mlog (fun () -> BU.print1 "unquote: tm = %s\n" (Print.term_to_string tm)) (fun _ ->
    bind (cur_goal ()) (fun goal ->
    let env = Env.set_expected_typ (goal_env goal) ty in
    bind (__tc_ghost env tm) (fun (tm, typ, guard) ->
    mlog (fun () -> BU.print1 "unquote: tm' = %s\n" (Print.term_to_string tm)) (fun _ ->
    mlog (fun () -> BU.print1 "unquote: typ = %s\n" (Print.term_to_string typ)) (fun _ ->
    bind (proc_guard "unquote" env guard) (fun () ->
    ret tm))))))

let uvar_env (env : env) (ty : option<typ>) : tac<term> =
    // If no type was given, add a uvar for it too!
    bind
        (match ty with
        | Some ty ->
          ret ty

        | None ->
          bind (new_uvar "uvar_env.2" env (fst <| U.type_u ()))
              (fun (typ, uvar_typ) -> //NS, FIXME discarding uvar_typ
                   ret typ)
        )
        (fun typ ->
            bind (new_uvar "uvar_env" env typ) (fun (t, uvar_t) ->
            ret t))

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


let unify_env (e:env) (t1 : term) (t2 : term) : tac<bool> = wrap_err "unify_env" <|
    bind get (fun ps ->
    bind (__tc e t1) (fun (t1, ty1, g1) ->
    bind (__tc e t2) (fun (t2, ty2, g2) ->
    bind (proc_guard "unify_env g1" e g1) (fun () ->
    bind (proc_guard "unify_env g2" e g2) (fun () ->
    tac_and (do_unify e ty1 ty2) (do_unify e t1 t2))))))

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
    bind (cur_goal ()) (fun g ->
    bind (__tc (goal_env g) ty) (fun (ty, _, guard) ->
    bind (proc_guard "change" (goal_env g) guard) (fun () ->
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
    bind (cur_goal ()) (fun g ->
    bind (__tc (goal_env g) s_tm) (fun (s_tm, s_ty, guard) ->
    bind (proc_guard "destruct" (goal_env g) guard) (fun () ->
    let h, args = U.head_and_args' s_ty in
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
                        let subst = List.map (fun ((bv, _), (t, _)) -> NT (bv, t)) d_ps_a_ps in
                        let bs = SS.subst_binders subst bs in
                        let subpats_1 = List.map (fun ((bv, _), (t, _)) ->
                                                 (mk_pat (Pat_dot_term (bv, t)), true)) d_ps_a_ps in
                        let subpats_2 = List.map (fun (bv, aq) ->
                                                 (mk_pat (Pat_var bv), is_imp aq)) bs in
                        let subpats = subpats_1 @ subpats_2 in
                        let pat = mk_pat (Pat_cons (fv, subpats)) in
                        let env = (goal_env g) in


                        (* Add an argument stating the equality between the scrutinee
                         * and the pattern, in-scope for this branch. *)
                        let cod = goal_type g in
                        let equ = env.universe_of env s_ty in
                        (* Typecheck the pattern, to fill-in the universes and get an expression out of it *)
                        let _ , _, _, pat_t, _, _guard_pat = TcTerm.tc_pat ({ env with lax = true }) s_ty pat in
                        let eq_b = S.gen_bv "breq" None (U.mk_squash equ (U.mk_eq2 equ s_ty s_tm pat_t)) in
                        let cod = U.arrow [S.mk_binder eq_b] (mk_Total cod) in

                        let nty = U.arrow bs (mk_Total cod) in
                        bind (new_uvar "destruct branch" env nty) (fun (uvt, uv) ->
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
      let w = mk (Tm_match (s_tm, brs)) None s_tm.pos in
      bind (solve' g w) (fun () ->
      bind (add_goals goals) (fun () ->
      ret infos))))

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
        ret <| Tv_App (S.mk_Tm_app hd (init args) None t.pos, (a, q')) // TODO: The range and tk are probably wrong. Fix

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
        ret <| Tv_Refine (fst b, t)

    | Tm_constant c ->
        ret <| Tv_Const (inspect_const c)

    | Tm_uvar (ctx_u, s) ->
        ret <| Tv_Uvar (Z.of_int_fs (UF.uvar_id ctx_u.ctx_uvar_head), (ctx_u, s))

    | Tm_let ((false, [lb]), t2) ->
        if lb.lbunivs <> [] then ret <| Tv_Unknown else
        begin match lb.lbname with
        | BU.Inr _ -> ret <| Tv_Unknown // no top level lets
        | BU.Inl bv ->
            // The type of `bv` should match `lb.lbtyp`
            let b = S.mk_binder bv in
            let bs, t2 = SS.open_term [b] t2 in
            let b = match bs with
                    | [b] -> b
                    | _ -> failwith "impossible: open_term returned different amount of binders"
            in
            ret <| Tv_Let (false, fst b, lb.lbdef, t2)
        end

    | Tm_let ((true, [lb]), t2) ->
        if lb.lbunivs <> [] then ret <| Tv_Unknown else
        begin match lb.lbname with
        | BU.Inr _ -> ret <| Tv_Unknown // no top level lets
        | BU.Inl bv ->
            let lbs, t2 = SS.open_let_rec [lb] t2 in
            match lbs with
            | [lb] ->
                (match lb.lbname with
                 | BU.Inr _ -> ret Tv_Unknown
                 | BU.Inl bv -> ret <| Tv_Let (true, bv, lb.lbdef, t2))
            | _ -> failwith "impossible: open_term returned different amount of binders"
        end

    | Tm_match (t, brs) ->
        let rec inspect_pat p =
            match p.v with
            | Pat_constant c -> Pat_Constant (inspect_const c)
            | Pat_cons (fv, ps) -> Pat_Cons (fv, List.map (fun (p, _) -> inspect_pat p) ps)
            | Pat_var bv -> Pat_Var bv
            | Pat_wild bv -> Pat_Wild bv
            | Pat_dot_term (bv, t) -> Pat_Dot_Term (bv, t)
        in
        let brs = List.map SS.open_branch brs in
        let brs = List.map (function (pat, _, t) -> (inspect_pat pat, t)) brs in
        ret <| Tv_Match (t, brs)

    | Tm_unknown ->
        ret <| Tv_Unknown

    | _ ->
        Err.log_issue t.pos (Err.Warning_CantInspect, BU.format2 "inspect: outside of expected syntax (%s, %s)\n" (Print.tag_of_term t) (Print.term_to_string t));
        ret <| Tv_Unknown
    )

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
        ret <| S.mk (Tm_constant (pack_const c)) None Range.dummyRange

    | Tv_Uvar (_u, ctx_u_s) ->
        ret <| S.mk (Tm_uvar ctx_u_s) None Range.dummyRange

    | Tv_Let (false, bv, t1, t2) ->
        let lb = U.mk_letbinding (BU.Inl bv) [] bv.sort PC.effect_Tot_lid t1 [] Range.dummyRange in
        ret <| S.mk (Tm_let ((false, [lb]), SS.close [S.mk_binder bv] t2)) None Range.dummyRange

    | Tv_Let (true, bv, t1, t2) ->
        let lb = U.mk_letbinding (BU.Inl bv) [] bv.sort PC.effect_Tot_lid t1 [] Range.dummyRange in
        let lbs, body = SS.close_let_rec [lb] t2 in
        ret <| S.mk (Tm_let ((true, lbs), body)) None Range.dummyRange

    | Tv_Match (t, brs) ->
        let wrap v = {v=v;p=Range.dummyRange} in
        let rec pack_pat p : S.pat =
            match p with
            | Pat_Constant c -> wrap <| Pat_constant (pack_const c)
            | Pat_Cons (fv, ps) -> wrap <| Pat_cons (fv, List.map (fun p -> pack_pat p, false) ps)
            | Pat_Var  bv -> wrap <| Pat_var bv
            | Pat_Wild bv -> wrap <| Pat_wild bv
            | Pat_Dot_Term (bv, t) -> wrap <| Pat_dot_term (bv, t)
        in
        let brs = List.map (function (pat, t) -> (pack_pat pat, None, t)) brs in
        let brs = List.map SS.close_branch brs in
        ret <| S.mk (Tm_match (t, brs)) None Range.dummyRange

    | Tv_AscribedT(e, t, tacopt) ->
        ret <| S.mk (Tm_ascribed(e, (BU.Inl t, tacopt), None)) None Range.dummyRange

    | Tv_AscribedC(e, c, tacopt) ->
        ret <| S.mk (Tm_ascribed(e, (BU.Inr c, tacopt), None)) None Range.dummyRange

    | Tv_Unknown ->
        ret <| S.mk Tm_unknown None Range.dummyRange

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

let goal_of_goal_ty env typ : goal * guard_t =
    let u, ctx_uvars, g_u = TcUtil.new_implicit_var "proofstate_of_goal_ty" typ.pos env typ in
    let ctx_uvar, _ = List.hd ctx_uvars in
    let g = mk_goal env ctx_uvar (FStar.Options.peek()) false "" in
    g, g_u

let proofstate_of_goal_ty rng env typ =
    let g, g_u = goal_of_goal_ty env typ in
    let ps = {
        main_context = env;
        main_goal = g;
        all_implicits = g_u.implicits;
        goals = [g];
        smt_goals = [];
        depth = 0;
        __dump = (fun ps msg -> dump_proofstate ps msg);
        psc = Cfg.null_psc;
        entry_range = rng;
        guard_policy = SMT;
        freshness = 0;
        tac_verb_dbg = Env.debug env (Options.Other "TacVerbose");
        local_state = BU.psmap_empty ();
    }
    in
    (ps, (goal_witness g))

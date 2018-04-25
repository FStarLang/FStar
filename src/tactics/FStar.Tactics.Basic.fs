﻿#light "off"
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
module N = FStar.TypeChecker.Normalize
module UF = FStar.Syntax.Unionfind
module EMB = FStar.Syntax.Embeddings
module Err = FStar.Errors
module Z = FStar.BigInt
open FStar.Reflection.Data
open FStar.Reflection.Basic

// working around #1374
type goal = FStar.Tactics.Types.goal

type name = bv
type env = Env.env
type implicits = Env.implicits

// Beta reduce
let normalize s e t = N.normalize_with_primitive_steps FStar.Reflection.Interpreter.reflection_primops s e t
let bnorm e t = normalize [] e t
let tts = N.term_to_string

open FStar.Tactics.Types
open FStar.Tactics.Result

(* The main monad for tactics.
 * A record, so we can keep it somewhat encapsulated and
 * can more easily add things to it if need be.
 *)
type tac<'a> = {
    tac_f : proofstate -> __result<'a>;
}

let mk_tac (f : proofstate -> __result<'a>) : tac<'a> =
    { tac_f = f }

let run t p = t.tac_f p

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

let goal_to_string (g:goal) =
    let g_binders = Env.all_binders g.context |> Print.binders_to_string ", " in
    let w = bnorm g.context g.witness in
    let t = bnorm g.context g.goal_ty in
    Util.format3 "%s |- %s : %s" g_binders (tts g.context w) (tts g.context t)

let tacprint  (s:string)       = BU.print1 "TAC>> %s\n" s
let tacprint1 (s:string) x     = BU.print1 "TAC>> %s\n" (BU.format1 s x)
let tacprint2 (s:string) x y   = BU.print1 "TAC>> %s\n" (BU.format2 s x y)
let tacprint3 (s:string) x y z = BU.print1 "TAC>> %s\n" (BU.format3 s x y z)

let comp_to_typ (c:comp) : typ =
    match c.n with
    | Total (t, _)
    | GTotal (t, _) -> t
    | Comp ct -> ct.result_typ

let is_irrelevant (g:goal) : bool =
    match U.un_squash (N.unfold_whnf g.context g.goal_ty) with
    | Some t -> true
    | _ -> false

let print (msg:string) : tac<unit> =
    tacprint msg;
    ret ()

let debug (msg:string) : tac<unit> =
    bind get (fun ps ->
    if Options.debug_module (Ident.string_of_lid ps.main_context.curmodule)
    then tacprint msg
    else ();
    ret ())

let dump_goal ps goal =
    tacprint (goal_to_string goal);
    ()

let dump_cur ps msg =
    match ps.goals with
    | [] ->
        tacprint1 "No more goals (%s)" msg
    | h::_ ->
        begin
        tacprint1 "Current goal (%s):" msg;
        dump_goal ps (List.hd ps.goals)
        end

let ps_to_string (msg, ps) =
    String.concat ""
               [format2 "State dump @ depth %s (%s):\n" (string_of_int ps.depth) msg;
                format1 "Location: %s\n" (Range.string_of_range ps.entry_range);
                format2 "ACTIVE goals (%s):\n%s\n"
                    (string_of_int (List.length ps.goals))
                    (String.concat "\n" (List.map goal_to_string ps.goals));
                format2 "SMT goals (%s):\n%s\n"
                    (string_of_int (List.length ps.smt_goals))
                    (String.concat "\n" (List.map goal_to_string ps.smt_goals));
               ]

let goal_to_json g =
    let g_binders = Env.all_binders g.context |> Print.binders_to_json (Env.dsenv g.context) in
    JsonAssoc [("hyps", g_binders);
               ("goal", JsonAssoc [("witness", JsonStr (tts g.context g.witness));
                                   ("type", JsonStr (tts g.context g.goal_ty))])]

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

let print_proof_state1  (msg:string) : tac<unit> =
    mk_tac (fun ps ->
                   let psc = ps.psc in
                   let subst = N.psc_subst psc in
                   dump_cur (subst_proof_state subst ps) msg;
                   Success ((), ps))

let print_proof_state (msg:string) : tac<unit> =
    mk_tac (fun ps ->
                   let psc = ps.psc in
                   let subst = N.psc_subst psc in
                   dump_proofstate (subst_proof_state subst ps) msg;
                   Success ((), ps))

let tac_verb_dbg : ref<option<bool>> = BU.mk_ref None
let rec log ps f : unit =
    match !tac_verb_dbg with
    | None -> (tac_verb_dbg := Some (Env.debug ps.main_context (Options.Other "TacVerbose"));
               log ps f)
    | Some true -> f ()
    | Some false -> ()

let mlog f (cont : unit -> tac<'a>) : tac<'a> =
    bind get (fun ps -> log ps f; cont ())

let fail (msg:string) =
    mk_tac (fun ps ->
        if Env.debug ps.main_context (Options.Other "TacFail")
        then dump_proofstate ps ("TACTIC FAILING: " ^ msg);
        Failed (msg, ps)
    )

let fail1 msg x     = fail (BU.format1 msg x)
let fail2 msg x y   = fail (BU.format2 msg x y)
let fail3 msg x y z = fail (BU.format3 msg x y z)
let fail4 msg x y z w = fail (BU.format4 msg x y z w)

let trytac' (t : tac<'a>) : tac<either<string,'a>> =
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
let trytac (t : tac<'a>) : tac<option<'a>> =
    bind (trytac' t) (fun r ->
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

// This is relying on the fact that errors are strings
let wrap_err (pref:string) (t : tac<'a>) : tac<'a> =
    mk_tac (fun ps ->
            match run t ps with
            | Success (a, q) ->
                Success (a, q)
            | Failed (msg, q) ->
                Failed (pref ^ ": " ^ msg, q)
           )

////////////////////////////////////////////////////////////////////
(* Some TRUSTED internal utilities *)

(* set : set the current proof state; shouldn't be exposed externally *)
let set (p:proofstate) : tac<unit> =
    mk_tac (fun _ -> Success ((), p))

let __do_unify (env : env) (t1 : term) (t2 : term) : tac<bool> =
    let _ = if Env.debug env (Options.Other "1346") then
                  BU.print2 "%%%%%%%%do_unify %s =? %s\n"
                            (Print.term_to_string t1)
                            (Print.term_to_string t2) in
    try
            let res = Rel.teq_nosmt env t1 t2 in
            if Env.debug env (Options.Other "1346")
            then (BU.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                                  (string_of_bool res)
                                  (Print.term_to_string t1)
                                  (Print.term_to_string t2));
            ret res
    with | Errors.Err (_, msg) -> begin
            mlog (fun () -> BU.print1 ">> do_unify error, (%s)\n" msg ) (fun _ ->
            ret false)
            end
         | Errors.Error (_, msg, r) -> begin
            mlog (fun () -> BU.print2 ">> do_unify error, (%s) at (%s)\n"
                                msg (Range.string_of_range r)) (fun _ ->
            ret false)
            end

let do_unify env t1 t2 : tac<bool> =
    bind idtac (fun () ->
    if Env.debug env (Options.Other "1346") then (
        Options.push ();
        let _ = Options.set_options Options.Set "--debug_level Rel --debug_level RelCheck" in
        ()
    );

    bind (
        bind (__do_unify env t1 t2) (fun b ->
        if not b
        then let t1 = N.normalize [] env t1 in
             let t2 = N.normalize [] env t2 in
             __do_unify env t1 t2
        else ret b)) (fun r ->

    if Env.debug env (Options.Other "1346") then
        Options.pop ();
    ret r))

let trysolve (goal : goal) (solution : term) : tac<bool> =
    do_unify goal.context solution goal.witness

let __dismiss : tac<unit> =
    bind get (fun p ->
    set ({p with goals=List.tl p.goals}))

let dismiss () : tac<unit> =
    bind get (fun p ->
    match p.goals with
    | [] -> fail "dismiss: no more goals"
    | _ -> __dismiss)

let solve (goal : goal) (solution : term) : tac<unit> =
    bind (trysolve goal solution) (fun b ->
    if b
    then __dismiss
    else fail (BU.format3 "%s does not solve %s : %s"
              (tts goal.context solution)
              (tts goal.context goal.witness)
              (tts goal.context goal.goal_ty)))

let dismiss_all : tac<unit> =
    bind get (fun p ->
    set ({p with goals=[]}))

let nwarn = BU.mk_ref 0

let check_valid_goal g =
    if Options.defensive () then begin
        let b = true in
        let env = g.context in
        let b = b && Env.closed env g.witness in
        let b = b && Env.closed env g.goal_ty in
        let rec aux b e =
            match Env.pop_bv e with
            | None -> b
            | Some (bv, e) -> (
                let b = b && Env.closed e bv.sort in
                aux b e
                )
        in
        if not (aux b env) && !nwarn < 5
        then (Err.log_issue g.goal_ty.pos
                  (Errors.Warning_IllFormedGoal, BU.format1 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                              (goal_to_string g));
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

let add_implicits (i:implicits) : tac<unit> =
    bind get (fun p ->
    set ({p with all_implicits=i@p.all_implicits}))

let new_uvar (reason:string) (env:env) (typ:typ) : tac<term> =
    let u, _, g_u = TcUtil.new_implicit_var reason typ.pos env typ in
    bind (add_implicits g_u.implicits) (fun _ ->
    ret u)

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
    | hd::tl -> ret hd)

let tadmit () : tac<unit> = wrap_err "tadmit" <|
    bind (cur_goal ()) (fun g ->
    Err.log_issue g.goal_ty.pos
        (Errors.Warning_TacAdmit, BU.format1 "Tactics admitted goal <%s>\n\n"
                    (goal_to_string g));
    solve g U.exp_unit)

let fresh () : tac<Z.t> =
    bind get (fun ps ->
    let n = ps.freshness in
    let ps = { ps with freshness = n + 1 } in
    bind (set ps) (fun () ->
    ret (Z.of_int_fs n)))

let ngoals () : tac<Z.t> =
    bind get (fun ps ->
    let n = List.length ps.goals in
    ret (Z.of_int_fs n))

let ngoals_smt () : tac<Z.t> =
    bind get (fun ps ->
    let n = List.length ps.smt_goals in
    ret (Z.of_int_fs n))

let is_guard () : tac<bool> =
    bind (cur_goal ()) (fun g ->
    ret g.is_guard)

let mk_irrelevant_goal (reason:string) (env:env) (phi:typ) opts : tac<goal> =
    let typ = U.mk_squash (env.universe_of env phi) phi in
    bind (new_uvar reason env typ) (fun u ->
    let goal = { context = env; witness = u; goal_ty = typ; opts = opts; is_guard = false } in
    ret goal)

let __tc (e : env) (t : term) : tac<(term * typ * guard_t)> =
    bind get (fun ps ->
    mlog (fun () -> BU.print1 "Tac> __tc(%s)\n" (tts e t)) (fun () ->
    try ret (ps.main_context.type_of e t)
    with | Errors.Err (_, msg)
         | Errors.Error (_, msg, _) -> begin
           fail3 "Cannot type %s in context (%s). Error = (%s)" (tts e t)
                                                  (Env.all_binders e |> Print.binders_to_string ", ")
                                                  msg
           end))

let istrivial (e:env) (t:term) : bool =
    let steps = [N.Reify; N.UnfoldUntil Delta_constant; N.Primops; N.Simplify; N.UnfoldTac; N.Unmeta] in
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

let proc_guard (reason:string) (e : env) (g : guard_t) opts : tac<unit> =
    match (Rel.simplify_guard e g).guard_f with
    | TcComm.Trivial -> ret ()
    | TcComm.NonTrivial f ->
        if istrivial e f // trivializes further...
        then ret ()
        else // check the policy
    bind get (fun ps ->
    match ps.guard_policy with
    | Drop -> ret () // should somehow taint
    | Goal ->
        bind (mk_irrelevant_goal reason e f opts) (fun goal ->
        let goal = { goal with is_guard = true } in
        push_goals [goal])
    | SMT ->
        bind (mk_irrelevant_goal reason e f opts) (fun goal ->
        let goal = { goal with is_guard = true } in
        push_smt_goals [goal])
    | Force ->
        try if not (Rel.is_trivial <| Rel.discharge_guard_no_smt e g)
            then
                mlog (fun () -> BU.print1 "guard = %s\n" (Rel.guard_to_string e g)) (fun () ->
                fail1 "Forcing the guard failed %s)" reason)
            else ret ()
        with
        | _ -> mlog (fun () -> BU.print1 "guard = %s\n" (Rel.guard_to_string e g)) (fun () ->
               fail1 "Forcing the guard failed (%s)" reason))

let tc (t : term) : tac<typ> = wrap_err "tc" <|
    bind (cur_goal ()) (fun goal ->
    bind (__tc goal.context t) (fun (t, typ, guard) ->
    bind (proc_guard "tc" goal.context guard goal.opts) (fun _ ->
    ret typ
    )))

let add_irrelevant_goal reason env phi opts : tac<unit> =
    bind (mk_irrelevant_goal reason env phi opts) (fun goal ->
    add_goals [goal])

let trivial () : tac<unit> =
    bind (cur_goal ()) (fun goal ->
    if istrivial goal.context goal.goal_ty
    then solve goal U.exp_unit
    else fail1 "Not a trivial goal: %s" (tts goal.context goal.goal_ty)
    )

let goal_from_guard (reason:string) (e:env) (g : guard_t) opts : tac<option<goal>> =
    match (Rel.simplify_guard e g).guard_f with
    | TcComm.Trivial -> ret None
    | TcComm.NonTrivial f ->
        if istrivial e f then ret None else
        bind (mk_irrelevant_goal reason e f opts) (fun goal ->
        ret (Some ({ goal with is_guard = true })))

let smt () : tac<unit> =
    bind (cur_goal ()) (fun g ->
    if is_irrelevant g then
        bind __dismiss (fun _ -> add_smt_goals [g])
    else
        fail1 "goal is not irrelevant: cannot dispatch to smt (%s)" (tts g.context g.goal_ty)
    )

let divide (n:Z.t) (l : tac<'a>) (r : tac<'b>) : tac<('a * 'b)> =
    bind get (fun p ->
    bind (try ret (List.splitAt (Z.to_int_fs n) p.goals) with | _ -> fail "divide: not enough goals") (fun (lgs, rgs) ->
    let lp = {p with goals=lgs; smt_goals=[]} in
    let rp = {p with goals=rgs; smt_goals=[]} in
    bind (set lp) (fun _ ->
    bind l        (fun a ->
    bind get      (fun lp' ->
    bind (set rp) (fun _ ->
    bind r        (fun b ->
    bind get      (fun rp' ->
    let p' = {p with goals=lp'.goals@rp'.goals; smt_goals=lp'.smt_goals@rp'.smt_goals@p.smt_goals} in
    bind (set p') (fun _ ->
    ret (a, b))))))))))

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

let intro () : tac<binder> = wrap_err "intro" <|
    bind (cur_goal ()) (fun goal ->
    match U.arrow_one goal.goal_ty with
    | Some (b, c) ->
        if not (U.is_total_comp c)
        then fail "Codomain is effectful"
        else let env' = Env.push_binders goal.context [b] in
             let typ' = comp_to_typ c in
             bind (new_uvar "intro" env' typ') (fun u ->
             bind (trysolve goal (U.abs [b] u None)) (fun bb ->
             if bb
             then bind (replace_cur ({ goal with context = env';
                                                 goal_ty = bnorm env' typ';
                                                 witness = bnorm env' u})) (fun _ ->
                  ret b)
             else fail "unification failed"
             ))
    | None ->
        fail1 "goal is not an arrow (%s)" (tts goal.context goal.goal_ty)
    )

// TODO: missing: precedes clause, and somehow disabling fixpoints only as needed
let intro_rec () : tac<(binder * binder)> =
    bind (cur_goal ()) (fun goal ->
    BU.print_string "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
    BU.print_string "WARNING (intro_rec): proceed at your own risk...\n";
    match U.arrow_one goal.goal_ty with
    | Some (b, c) ->
        if not (U.is_total_comp c)
        then fail "Codomain is effectful"
        else let bv = gen_bv "__recf" None goal.goal_ty in
             let bs = [S.mk_binder bv; b] in // recursively bound name and argument we're introducing
             let env' = Env.push_binders goal.context bs in
             bind (new_uvar "intro_rec" env' (comp_to_typ c)) (fun u ->
             let lb = U.mk_letbinding (Inl bv) [] goal.goal_ty PC.effect_Tot_lid (U.abs [b] u None) [] Range.dummyRange in
             let body = S.bv_to_name bv in
             let lbs, body = SS.close_let_rec [lb] body in
             let tm = mk (Tm_let ((true, lbs), body)) None goal.witness.pos in
             bind (trysolve goal tm) (fun bb ->
             if bb
             then bind (replace_cur ({ goal with context = env';
                                                 goal_ty = bnorm env' (comp_to_typ c);
                                                 witness = bnorm env' u})) (fun _ ->
                  ret (S.mk_binder bv, b))
             else fail "intro_rec: unification failed"
             ))
    | None ->
        fail1 "intro_rec: goal is not an arrow (%s)" (tts goal.context goal.goal_ty)
    )

let norm (s : list<EMB.norm_step>) : tac<unit> =
    bind (cur_goal ()) (fun goal ->
    mlog (fun () -> BU.print1 "norm: witness = %s\n" (Print.term_to_string goal.witness)) (fun _ ->
    // Translate to actual normalizer steps
    let steps = [N.Reify; N.UnfoldTac]@(N.tr_norm_steps s) in
    let w = normalize steps goal.context goal.witness in
    let t = normalize steps goal.context goal.goal_ty in
    replace_cur ({goal with goal_ty = t; witness = w})
    ))

let norm_term_env (e : env) (s : list<EMB.norm_step>) (t : term) : tac<term> = wrap_err "norm_term" <|
    mlog (fun () -> BU.print1 "norm_term: tm = %s\n" (Print.term_to_string t)) (fun _ ->
    bind get (fun ps ->
    (* We need a set of options, but there might be no goals, so do this *)
    let opts = match ps.goals with
               | g::_ -> g.opts
               | _ -> FStar.Options.peek ()
    in
    mlog (fun () -> BU.print1 "norm_term_env: t = %s\n" (tts ps.main_context t)) (fun () ->
    bind (__tc e t) (fun (t, _, _) ->
    let steps = [N.Reify; N.UnfoldTac]@(N.tr_norm_steps s) in
    let t = normalize steps ps.main_context t in
    ret t
    ))))

let refine_intro () : tac<unit> = wrap_err "refine_intro" <|
    bind (cur_goal ()) (fun g ->
    match Rel.base_and_refinement g.context g.goal_ty with
    | _, None -> fail "not a refinement"
    | t, Some (bv, phi) ->
        let g1 = { g with goal_ty = t } in
        let bv, phi = match SS.open_term [S.mk_binder bv] phi with
                      | bvs, phi -> fst (List.hd bvs), phi
        in
        bind (mk_irrelevant_goal "refine_intro refinement" g.context
                    (SS.subst [S.NT (bv, g.witness)] phi) g.opts) (fun g2 ->
        bind __dismiss (fun _ ->
        add_goals [g1;g2])))

let __exact_now set_expected_typ (t:term) : tac<unit> =
    bind (cur_goal ()) (fun goal ->
    let env = if set_expected_typ
              then Env.set_expected_typ goal.context goal.goal_ty
              else goal.context
    in
    bind (__tc env t) (fun (t, typ, guard) ->
    mlog (fun () -> BU.print2 "__exact_now: got type %s\n__exact_now and guard %s\n"
                                                     (tts goal.context typ)
                                                     (Rel.guard_to_string goal.context guard)) (fun _ ->
    bind (proc_guard "__exact typing" goal.context guard goal.opts) (fun _ ->
    mlog (fun () -> BU.print2 "__exact_now: unifying %s and %s\n" (tts goal.context typ)
                                                                  (tts goal.context goal.goal_ty)) (fun _ ->
    bind (do_unify goal.context typ goal.goal_ty) (fun b -> if b
    then solve goal t
    else fail4 "%s : %s does not exactly solve the goal %s (witness = %s)"
                    (tts goal.context t)
                    (tts goal.context typ)
                    (tts goal.context goal.goal_ty)
                    (tts goal.context goal.witness)))))))

let t_exact set_expected_typ tm : tac<unit> = wrap_err "exact" <|
    mlog (fun () -> BU.print1 "t_exact: tm = %s\n" (Print.term_to_string tm)) (fun _ ->
    bind (trytac' (__exact_now set_expected_typ tm)) (function
    | Inr r -> ret r
    | Inl e ->
    bind (trytac' (bind (norm [EMB.Delta]) (fun _ ->
                   bind (refine_intro ()) (fun _ ->
                   __exact_now set_expected_typ tm)))) (function
    | Inr r -> ret r
    | Inl _ -> fail e))) // keep original error

let uvar_free_in_goal (u:uvar) (g:goal) =
    if g.is_guard then false else
    let free_uvars = List.map fst (BU.set_elements (SF.uvars g.goal_ty)) in
    List.existsML (UF.equiv u) free_uvars

let uvar_free (u:uvar) (ps:proofstate) : bool =
    List.existsML (uvar_free_in_goal u) ps.goals

let rec mapM (f : 'a -> tac<'b>) (l : list<'a>) : tac<list<'b>> =
    match l with
    | [] -> ret []
    | x::xs ->
        bind (f x) (fun y ->
        bind (mapM f xs) (fun ys ->
        ret (y::ys)))

exception NoUnif

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
// without asking for ?u first, which will most likely be instantiated when
// solving any of these two goals. In any case, if ?u is not solved, we fail afterwards.
// TODO: this should probably be made into a user tactic
let rec __apply (uopt:bool) (tm:term) (typ:typ) : tac<unit> =
    bind (cur_goal ()) (fun goal ->
    mlog (fun () -> BU.print1 ">>> Calling __exact(%s)\n" (Print.term_to_string tm)) (fun () ->
    bind (trytac_exn (with_policy Force (t_exact false tm))) (function
    | Some r -> ret r // if tm is a solution, we're done
    | None ->
        // exact failed, try to instantiate more arguments
        mlog (fun () -> BU.print1 ">>> typ = %s\n" (Print.term_to_string typ)) (fun () ->
        match U.arrow_one typ with
        | None -> raise NoUnif
        | Some ((bv, aq), c) ->
            mlog (fun () ->
                BU.print1 "__apply: pushing binder %s\n" (Print.binder_to_string (bv, aq))) (fun _ ->
            if not (U.is_total_comp c) then fail "apply: not total codomain" else
            bind (new_uvar "apply" goal.context bv.sort) (fun u ->
            (* BU.print1 "__apply: witness is %s\n" (Print.term_to_string u); *)
            let tm' = mk_Tm_app tm [(u, aq)] None tm.pos in
            let typ' = SS.subst [S.NT (bv, u)] <| comp_to_typ c in
            bind (__apply uopt tm' typ') (fun _ ->
            let u = bnorm goal.context u in
            match (SS.compress (fst (U.head_and_args u))).n with
            | Tm_uvar (uvar, _) ->
                bind get (fun ps ->
                if uopt && uvar_free uvar ps
                then ret ()
                else begin
                    (* BU.print2 "__apply: adding goal %s : %s\n" (Print.term_to_string u) *)
                    (*                                            (Print.term_to_string bv.sort); *)
                    add_goals [{ goal with
                                  witness  = bnorm goal.context u;
                                  goal_ty  = bnorm goal.context bv.sort;
                                  is_guard = false; }]
                end)
            | t -> begin
                (* BU.print1 "__apply: uvar was instantiated to %s\n" (Print.term_to_string u); *)
                ret ()
                end
            )))))))

// The exception is thrown only when the tactic runs, not when it's defined,
// so we need to do this to catch it
let try_unif (t : tac<'a>) (t' : tac<'a>) : tac<'a> =
    mk_tac (fun ps ->
        try run t ps
        with NoUnif -> run t' ps)

let apply (uopt:bool) (tm:term) : tac<unit> = wrap_err "apply" <|
    mlog (fun () -> BU.print1 "apply: tm = %s\n" (Print.term_to_string tm)) (fun _ ->
    bind (cur_goal ()) (fun goal ->
    bind (__tc goal.context tm) (fun (tm, typ, guard) ->
    // Focus helps keep the goal order
    let typ = bnorm goal.context typ in
    try_unif (focus (bind (__apply uopt tm typ) (fun _ -> proc_guard "apply guard" goal.context guard goal.opts)))
             (fail3 "Cannot instantiate %s (of type %s) to match goal (%s)"
                            (tts goal.context tm)
                            (tts goal.context typ)
                            (tts goal.context goal.goal_ty))
    )))

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

let apply_lemma (tm:term) : tac<unit> = wrap_err "apply_lemma" <| focus (
    mlog (fun () -> BU.print1 "apply_lemma: tm = %s\n" (Print.term_to_string tm)) (fun _ ->
    let is_unit_t t = match (SS.compress t).n with
    | Tm_fvar fv when S.fv_eq_lid fv PC.unit_lid -> true
    | _ -> false
    in
    bind (cur_goal ()) (fun goal ->
    bind (__tc goal.context tm) (fun (tm, t, guard) ->
    let bs, comp = U.arrow_formals_comp t in
    match lemma_or_sq comp with
    | None -> fail "not a lemma or squashed function"
    | Some (pre, post) ->
    let uvs, implicits, subst =
       List.fold_left (fun (uvs, guard, subst) (b, aq) ->
               let b_t = SS.subst subst b.sort in
               if is_unit_t b_t
               then
                   // Simplification: if the argument is simply unit, then don't ask for it
                   (U.exp_unit, aq)::uvs, guard, S.NT(b, U.exp_unit)::subst
               else
                   let u, _, g_u = TcUtil.new_implicit_var "apply_lemma" goal.goal_ty.pos goal.context b_t in
                   (u, aq)::uvs,
                   Rel.conj_guard guard g_u,
                   S.NT(b, u)::subst
               )
       ([], guard, [])
       bs
    in
    let uvs = List.rev uvs in
    let pre  = SS.subst subst pre in
    let post = SS.subst subst post in
    bind (do_unify goal.context (U.mk_squash U_zero post) goal.goal_ty) (fun b ->
    if not b
    then fail3 "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                            (tts goal.context tm)
                            (tts goal.context (U.mk_squash U_zero post))
                            (tts goal.context goal.goal_ty)
    else
       //NS: 01/24 ... looks redundant
       //let solution = N.normalize [N.Beta] goal.context (S.mk_Tm_app tm uvs None goal.context.range) in
        bind (add_implicits implicits.implicits) (fun _ ->
        // We solve with (), we don't care about the witness if applying a lemma
        bind (solve goal U.exp_unit) (fun _ ->
        let is_free_uvar uv t =
            let free_uvars = List.map fst (BU.set_elements (SF.uvars t)) in
            List.existsML (fun u -> UF.equiv u uv) free_uvars
        in
        let appears uv goals = List.existsML (fun g' -> is_free_uvar uv g'.goal_ty) goals in
        let checkone t goals =
            let hd, _ = U.head_and_args t in
            begin match hd.n with
            | Tm_uvar (uv, _) -> appears uv goals
            | _ -> false
            end
        in
        bind (implicits.implicits |> mapM (fun (_msg, env, _uvar, term, typ, _) ->
            let hd, _ = U.head_and_args term in
            match (SS.compress hd).n with
            | Tm_uvar _ ->
                ret ([{ goal with
                        witness = bnorm goal.context term;
                        goal_ty = bnorm goal.context typ //NS: 01/24 ...expensive
                       }], [])
            | _ ->
                let g_typ =
                  if Options.__temp_fast_implicits()
                  then // NS:01/24: use the fast path instead, knowing that term is at least well-typed
                       // NS:05/25: protecting it under this option,
                       //           since it causes a regression in examples/vale/*Math_i.fst
                       FStar.TypeChecker.TcTerm.check_type_of_well_typed_term false env term typ
                  else let term = bnorm env term in
                       let _, _, g_typ = env.type_of (Env.set_expected_typ env typ) term in
                       g_typ
                in
                bind (goal_from_guard "apply_lemma solved arg" goal.context g_typ goal.opts) (function
                | None -> ret ([], [])
                | Some g -> ret ([], [g])
                )
            )) (fun goals_ ->
        let sub_goals = List.flatten (List.map fst goals_) in
        let smt_goals = List.flatten (List.map snd goals_) in
        // Optimization: if a uvar appears in a later goal, don't ask for it, since
        // it will be instantiated later. TODO: maybe keep and check later?
        let rec filter' (f : 'a -> list<'a> -> bool) (xs : list<'a>) : list<'a> =
             match xs with
             | [] -> []
             | x::xs -> if f x xs then x::(filter' f xs) else filter' f xs
        in
        let sub_goals = filter' (fun g goals -> not (checkone g.witness goals)) sub_goals in
        bind (proc_guard "apply_lemma guard" goal.context guard goal.opts) (fun _ ->
        bind (if not (istrivial goal.context (U.mk_squash U_zero pre)) //lemma preconditions are in U_zero
              then add_irrelevant_goal "apply_lemma precondition" goal.context pre goal.opts
              else ret ()) (fun _ ->
        bind (add_smt_goals smt_goals) (fun _ ->
        add_goals sub_goals))))))
    )))))

let destruct_eq' (typ : typ) : option<(term * term)> =
    match U.destruct_typ_as_formula typ with
    | Some (U.BaseConn(l, [_; (e1, _); (e2, _)])) when Ident.lid_equals l PC.eq2_lid ->
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

let split_env (bvar : bv) (e : env) : option<(env * list<bv>)> =
    let rec aux e =
        match Env.pop_bv e with
        | None -> None
        | Some (bv', e') ->
            if S.bv_eq bvar bv'
            then Some (e', [])
            else map_opt (aux e') (fun (e'', bvs) -> (e'', bv'::bvs ))
    in
    map_opt (aux e) (fun (e', bvs) -> (e', List.rev bvs))

let push_bvs e bvs =
    List.fold_left (fun e b -> Env.push_bv e b) e bvs

let subst_goal (b1 : bv) (b2 : bv) (s:list<subst_elt>) (g:goal) : option<goal> =
    map_opt (split_env b1 g.context) (fun (e0, bvs) ->
        let s1 bv = { bv with sort = SS.subst s bv.sort } in
        let bvs = List.map s1 bvs in
        let c = push_bvs e0 (b2::bvs) in
        let w = SS.subst s g.witness in
        let t = SS.subst s g.goal_ty in
        { g with context = c; witness = w; goal_ty = t }
    )

let rewrite (h:binder) : tac<unit> =
    bind (cur_goal ()) (fun goal ->
    let bv, _ = h in
    mlog (fun _ -> BU.print2 "+++Rewrite %s : %s\n" (Print.bv_to_string bv) (tts goal.context bv.sort)) (fun _ ->
    match split_env bv goal.context with
    | None -> fail "rewrite: binder not found in environment"
    | Some (e0, bvs) -> begin
        match destruct_eq bv.sort with
        | Some (x, e) ->
        (match (SS.compress x).n with
           | Tm_name x ->
             let s = [NT(x,e)] in
             let s1 bv = { bv with sort = SS.subst s bv.sort } in
             let bvs = List.map s1 bvs in
             replace_cur ({goal with context = push_bvs e0 (bv::bvs);
                                     goal_ty = SS.subst s goal.goal_ty;
                                     witness = SS.subst s goal.witness;})
           | _ ->
             fail "rewrite: Not an equality hypothesis with a variable on the LHS")
        | _ -> fail "rewrite: Not an equality hypothesis"
        end))

let rename_to (b : binder) (s : string) : tac<unit> =
    bind (cur_goal ()) (fun goal ->
    let bv, _ = b in
    let bv' = freshen_bv ({ bv with ppname = mk_ident (s, bv.ppname.idRange) }) in
    let s = [NT (bv, S.bv_to_name bv')] in
    match subst_goal bv bv' s goal with
    | None -> fail "rename_to: binder not found in environment"
    | Some goal -> replace_cur goal)

let binder_retype (b : binder) : tac<unit> =
    bind (cur_goal ()) (fun goal ->
    let bv, _ = b in
    match split_env bv goal.context with
    | None -> fail "binder_retype: binder is not present in environment"
    | Some (e0, bvs) -> begin
        let (ty, u) = U.type_u () in
        bind (new_uvar "binder_retype" e0 ty) (fun t' ->
        let bv'' = {bv with sort = t'} in
        let s = [S.NT (bv, S.bv_to_name bv'')] in
        let bvs = List.map (fun b -> { b with sort = SS.subst s b.sort}) bvs in
        let env' = push_bvs e0 (bv''::bvs) in
        bind __dismiss (fun _ ->
        bind (add_goals [{goal with context = env';
                                    witness = SS.subst s goal.witness;
                                    goal_ty = SS.subst s goal.goal_ty }]) (fun _ ->
              add_irrelevant_goal "binder_retype equation" e0
                  (U.mk_eq2 (U_succ u) ty bv.sort t') goal.opts)))
         end)

(* TODO: move to bv *)
let norm_binder_type (s : list<EMB.norm_step>) (b : binder) : tac<unit> =
    bind (cur_goal ()) (fun goal ->
    let bv, _ = b in
    match split_env bv goal.context with
    | None -> fail "binder_retype: binder is not present in environment"
    | Some (e0, bvs) -> begin
        let steps = [N.Reify; N.UnfoldTac]@(N.tr_norm_steps s) in
        let sort' = normalize steps e0 bv.sort in
        let bv' = { bv with sort = sort' } in
        let env' = push_bvs e0 (bv'::bvs) in
        replace_cur ({ goal with context = env' })
        end
    )

let revert () : tac<unit> =
    bind (cur_goal ()) (fun goal ->
    match Env.pop_bv goal.context with
    | None -> fail "Cannot revert; empty context"
    | Some (x, env') ->
        let typ' = U.arrow [(x, None)] (mk_Total goal.goal_ty) in
        let w' = U.abs [(x, None)] goal.witness None in
        replace_cur ({ goal with context = env'; witness = w'; goal_ty = typ' })
    )

let free_in bv t =
    Util.set_mem bv (SF.names t)

let rec clear (b : binder) : tac<unit> =
    let bv = fst b in
    bind (cur_goal ()) (fun goal ->
    mlog (fun () -> BU.print2 "Clear of (%s), env has %s binders\n"
                        (Print.binder_to_string b)
                        (Env.all_binders goal.context |> List.length |> string_of_int)) (fun () ->
    match split_env bv goal.context with
    | None -> fail "Cannot clear; binder not in environment"
    | Some (e', bvs) ->
        let rec check bvs =
            match bvs with
            | [] -> ret ()
            | bv'::bvs ->
                if free_in bv bv'.sort
                then fail (BU.format1 "Cannot clear; binder present in the type of %s"
                                    (Print.bv_to_string bv'))
                else check bvs
        in
        if free_in bv goal.goal_ty then
            fail "Cannot clear; binder present in goal"
        else bind (check bvs) (fun () ->
        let env' = push_bvs e' bvs in
        bind (new_uvar "clear.witness" env' goal.goal_ty) (fun ut ->
        bind (do_unify goal.context goal.witness ut) (fun b ->
        if b
        then replace_cur ({ goal with context = env'; witness = ut })
        else fail "Cannot clear; binder appears in witness")))))

let clear_top () : tac<unit> =
    bind (cur_goal ()) (fun goal ->
    match Env.pop_bv goal.context with
    | None -> fail "Cannot clear; empty context"
    | Some (x, _) -> clear (S.mk_binder x)) // we ignore the qualifier anyway

let prune (s:string) : tac<unit> =
    bind (cur_goal ()) (fun g ->
    let ctx = g.context in
    let ctx' = Env.rem_proof_ns ctx (path_of_text s) in
    let g' = { g with context = ctx' } in
    bind __dismiss (fun _ -> add_goals [g']))

let addns (s:string) : tac<unit> =
    bind (cur_goal ()) (fun g ->
    let ctx = g.context in
    let ctx' = Env.add_proof_ns ctx (path_of_text s) in
    let g' = { g with context = ctx' } in
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
let pointwise_rec (ps : proofstate) (tau : tac<unit>) opts (env : Env.env) (t : term) : tac<term> =
    let t, lcomp, g = TcTerm.tc_term env t in
    if not (U.is_pure_or_ghost_lcomp lcomp) || not (Rel.is_trivial g) then
        ret t // Don't do anything for possibly impure terms
    else
        let rewrite_eq =
          let typ = lcomp.res_typ in
          bind (new_uvar "pointwise_rec" env typ) (fun ut ->
          log ps (fun () ->
              BU.print2 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n" (Print.term_to_string t)
                                                                   (Print.term_to_string ut));
          bind (add_irrelevant_goal "pointwise_rec equation" env
                                    (U.mk_eq2 (TcTerm.universe_of env typ) typ t ut) opts) (fun _ ->
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
       bind (trytac' rewrite_eq) (fun x ->
       match x with
       | Inl "SKIP" -> ret t
       | Inl e -> fail e
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
                opts
                (env : Env.env)
                (t : term) : ctrl_tac<term> =
    let t = SS.compress t in
    bind (bind (add_irrelevant_goal "dummy"
                    env
                    U.t_true
                    opts) (fun _ ->
          bind (ctrl t) (fun res ->
          bind (trivial ()) (fun _ ->
          ret res)))) (fun (should_rewrite, ctrl) ->
    if not should_rewrite
    then ret (t, ctrl)
    else let t, lcomp, g = TcTerm.tc_term env t in //re-typechecking the goal is expensive
         if not (U.is_pure_or_ghost_lcomp lcomp) || not (Rel.is_trivial g) then
           ret (t, globalStop) // Don't do anything for possibly impure terms
         else
           let typ = lcomp.res_typ in
           bind (new_uvar "pointwise_rec" env typ) (fun ut ->
           log ps (fun () ->
              BU.print2 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                (Print.term_to_string t) (Print.term_to_string ut));
           bind (add_irrelevant_goal
                             "rewrite_rec equation"
                             env
                             (U.mk_eq2 (TcTerm.universe_of env typ) typ t ut)
                             opts) (fun _ ->
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
                    (rewriter:tac<unit>) : tac<unit> =
    bind get (fun ps ->
    let g, gs = match ps.goals with
                | g::gs -> g, gs
                | [] -> failwith "Pointwise: no goals"
    in
    let gt = g.goal_ty in
    log ps (fun () ->
        BU.print1 "Topdown_rewrite starting with %s\n" (Print.term_to_string gt));
    bind dismiss_all (fun _ ->
    bind (ctrl_tac_fold (rewrite_rec ps ctrl rewriter g.opts) g.context keepGoing gt) (fun (gt', _) ->
    log ps (fun () ->
        BU.print1 "Topdown_rewrite seems to have succeded with %s\n" (Print.term_to_string gt'));
    bind (push_goals gs) (fun _ ->
    add_goals [{g with goal_ty = gt'}]))))


let pointwise (d : direction) (tau:tac<unit>) : tac<unit> =
    bind get (fun ps ->
    let g, gs = match ps.goals with
                | g::gs -> g, gs
                | [] -> failwith "Pointwise: no goals"
    in
    let gt = g.goal_ty in
    log ps (fun () ->
        BU.print1 "Pointwise starting with %s\n" (Print.term_to_string gt));
    bind dismiss_all (fun _ ->
    bind (tac_fold_env d (pointwise_rec ps tau g.opts) g.context gt) (fun gt' ->
    log ps (fun () ->
        BU.print1 "Pointwise seems to have succeded with %s\n" (Print.term_to_string gt'));
    bind (push_goals gs) (fun _ ->
    add_goals [{g with goal_ty = gt'}]))))

let trefl () : tac<unit> =
    bind (cur_goal ()) (fun g ->
    match U.un_squash g.goal_ty with
    | Some t ->
        begin
        let hd, args = U.head_and_args' t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [_; (l, _); (r, _)] when S.fv_eq_lid fv PC.eq2_lid ->
            bind (do_unify g.context l r) (fun b ->
            if not b
            then fail2 "trefl: not a trivial equality (%s vs %s)" (tts g.context l) (tts g.context r)
            else solve g U.exp_unit)
        | hd, _ ->
            fail1 "trefl: not an equality (%s)" (tts g.context t)
        end
     | None ->
        fail "not an irrelevant goal")

let dup () : tac<unit> =
    bind (cur_goal ()) (fun g ->
    bind (new_uvar "dup" g.context g.goal_ty) (fun u ->
    let g' = { g with witness = u } in
    bind __dismiss (fun _ ->
    bind (add_irrelevant_goal "dup equation" g.context
               (U.mk_eq2 (TcTerm.universe_of g.context g.goal_ty) g.goal_ty u g.witness) g.opts) (fun _ ->
    bind (add_goals [g']) (fun _ ->
    ret ())))))

let flip () : tac<unit> =
    bind get (fun ps ->
    match ps.goals with
    | g1::g2::gs -> set ({ps with goals=g2::g1::gs})
    | _ -> fail "flip: less than 2 goals"
    )

let later () : tac<unit> =
    bind get (fun ps ->
    match ps.goals with
    | [] -> ret ()
    | g::gs -> set ({ps with goals=gs@[g]})
    )

let qed () : tac<unit> =
    bind get (fun ps ->
    match ps.goals with
    | [] -> ret ()
    | _ -> fail "Not done!"
    )

let cases (t : term) : tac<(term * term)> = wrap_err "cases" <|
    bind (cur_goal ()) (fun g ->
    bind (__tc g.context t) (fun (t, typ, guard) ->
    let hd, args = U.head_and_args typ in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [(p, _); (q, _)] when S.fv_eq_lid fv PC.or_lid ->
        let v_p = S.new_bv None p in
        let v_q = S.new_bv None q in
        let g1 = {g with context = Env.push_bv g.context v_p } in
        let g2 = {g with context = Env.push_bv g.context v_q } in
        bind __dismiss (fun _ ->
        bind (add_goals [g1; g2]) (fun _ ->
        ret (S.bv_to_name v_p, S.bv_to_name v_q)))
    | _ ->
        fail1 "Not a disjunction: %s" (tts g.context typ)))

let set_options (s : string) : tac<unit> =
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
let cur_env     () : tac<env>  = bind (cur_goal ()) (fun g -> ret <| g.context)
let cur_goal'   () : tac<term> = bind (cur_goal ()) (fun g -> ret <| g.goal_ty)
let cur_witness () : tac<term> = bind (cur_goal ()) (fun g -> ret <| g.witness)

let unquote (ty : term) (tm : term) : tac<term> = wrap_err "unquote" <|
    bind (cur_goal ()) (fun goal ->
    let env = Env.set_expected_typ goal.context ty in
    bind (__tc env tm) (fun (tm, typ, guard) ->
    bind (proc_guard "unquote" env guard goal.opts) (fun () ->
    ret tm)))

let uvar_env (env : env) (ty : option<typ>) : tac<term> =
    // If no type was given, add a uvar for it too!
    bind (match ty with
    | Some ty -> ret ty
    | None -> new_uvar "uvar_env.2" env (fst <| U.type_u ())) (fun typ ->
    bind (new_uvar "uvar_env" env typ) (fun t ->
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
    | { n = Tm_uvar (_, typ) }, _ ->
        add_goals [{ witness  = bnorm env t;
                     goal_ty  = bnorm env typ;
                     is_guard = false;
                     context  = env;
                     opts     = opts; }]
    | _ -> fail "not a uvar")

let unify (t1 : term) (t2 : term) : tac<bool> =
    bind get (fun ps ->
    do_unify ps.main_context t1 t2)

let launch_process (prog : string) (args : list<string>) (input : string) : tac<string> =
    // The `bind idtac` thunks the tactic
    bind idtac (fun () ->
    if Options.unsafe_tactic_exec () then
        let s = BU.run_process "tactic_launch" prog args (Some input) in // FIXME
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
    bind (__tc g.context ty) (fun (ty, _, guard) ->
    bind (proc_guard "change" g.context guard g.opts) (fun () ->
    bind (do_unify g.context g.goal_ty ty) (fun bb ->
    if bb
    then replace_cur ({ g with goal_ty = ty })
    else begin
        (* Give it a second try, fully normalize the term the user gave
         * and unify it with the fully normalized goal. If that succeeds,
         * we use the original one as the new goal. This is sometimes needed
         * since the unifier has some bugs. *)
        let steps =
            [N.Reify; N.UnfoldUntil Delta_constant;
             N.AllowUnboundUniverses;
             N.Primops; N.Simplify; N.UnfoldTac; N.Unmeta] in
        let ng  = normalize steps g.context g.goal_ty in
        let nty = normalize steps g.context ty in
        bind (do_unify g.context ng nty) (fun b ->
        if b
        then replace_cur ({ g with goal_ty = ty })
        else fail "not convertible")
    end)))))

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
let rec inspect (t:term) : tac<term_view> =
    let t = U.unascribe t in
    let t = U.un_uinst t in
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
        failwith "inspect: empty arguments on Tm_app"

    | Tm_app (hd, args) ->
        // We split at the last argument, since the term_view does not
        // expose n-ary lambdas buy unary ones.
        let (a, q) = last args in
        let q' = inspect_aqual q in
        ret <| Tv_App (S.mk_Tm_app hd (init args) None t.pos, (a, q')) // TODO: The range and tk are probably wrong. Fix

    | Tm_abs ([], _, _) ->
        failwith "inspect: empty arguments on Tm_abs"

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
        failwith "inspect: empty binders on arrow"

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

    | Tm_uvar (u, t) ->
        ret <| Tv_Uvar (Z.of_int_fs (UF.uvar_id u), t)

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

    | Tv_Uvar (u, t) ->
        ret <| U.uvar_from_id (Z.to_int_fs u) t

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

let goal_of_goal_ty env typ : goal * guard_t =
    let u, _, g_u = TcUtil.new_implicit_var "proofstate_of_goal_ty" typ.pos env typ in
    let g = {
        context = env;
        witness = u;
        goal_ty = typ;
        opts    = FStar.Options.peek ();
        is_guard = false;
    }
    in
    g, g_u

let proofstate_of_goal_ty env typ =
    let g, g_u = goal_of_goal_ty env typ in
    let ps = {
        main_context = env;
        main_goal = g;
        all_implicits = g_u.implicits;
        goals = [g];
        smt_goals = [];
        depth = 0;
        __dump = (fun ps msg -> dump_proofstate ps msg);
        psc = N.null_psc;
        entry_range = Range.dummyRange;
        guard_policy = SMT;
        freshness = 0;
    }
    in
    (ps, g.witness)

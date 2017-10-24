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
module N = FStar.TypeChecker.Normalize
module RD = FStar.Reflection.Data
module UF = FStar.Syntax.Unionfind
module EMB = FStar.Syntax.Embeddings
module Err = FStar.Errors
module Z = FStar.BigInt

type name = bv
type env = Env.env
type implicits = Env.implicits

// Beta reduce
let normalize s e t = N.normalize_with_primitive_steps FStar.Reflection.Interpreter.reflection_primops s e t
let bnorm e t = normalize [] e t

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

let idtac : tac<unit> = ret ()

let goal_to_string (g:goal) =
    let g_binders = Env.all_binders g.context |> Print.binders_to_string ", " in
    let w = bnorm g.context g.witness in
    let t = bnorm g.context g.goal_ty in
    Util.format3 "%s |- %s : %s" g_binders (N.term_to_string g.context w) (N.term_to_string g.context t)

let tacprint  (s:string)       = BU.print1 "TAC>> %s\n" s
let tacprint1 (s:string) x     = BU.print1 "TAC>> %s\n" (BU.format1 s x)
let tacprint2 (s:string) x y   = BU.print1 "TAC>> %s\n" (BU.format2 s x y)
let tacprint3 (s:string) x y z = BU.print1 "TAC>> %s\n" (BU.format3 s x y z)

(* TODO: If I define this as *)
(*     (U.comp_to_comp_typ c).result_typ *)
(*     then I get  *)
(*     Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error. *)
(*     Assertion failed: Computation type without universe *)
let comp_to_typ (c:comp) : typ =
    match c.n with
    | Total (t, _)
    | GTotal (t, _) -> t
    | Comp ct -> ct.result_typ

let is_irrelevant (g:goal) : bool =
    match U.un_squash (N.unfold_whnf g.context g.goal_ty) with
    | Some t -> true
    | _ -> false

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

let ps_to_string (msg, ps) = format6 "State dump @ depth %s(%s):\nACTIVE goals (%s):\n%s\nSMT goals (%s):\n%s"
                (string_of_int ps.depth)
                msg (string_of_int (List.length ps.goals)) (String.concat "\n" (List.map goal_to_string ps.goals))
                (string_of_int (List.length ps.smt_goals)) (String.concat "\n" (List.map goal_to_string ps.smt_goals))
let goal_to_json g =
    let g_binders = Env.all_binders g.context |> Print.binders_to_json in
    JsonAssoc [("hyps", g_binders);
               ("goal", JsonAssoc [("witness", JsonStr (N.term_to_string g.context g.witness));
                                   ("type", JsonStr (N.term_to_string g.context g.goal_ty))])]

let ps_to_json (msg, ps) =
    JsonAssoc [("label", JsonStr msg);
               ("goals", JsonList (List.map goal_to_json ps.goals));
               ("smt-goals", JsonList (List.map goal_to_json ps.smt_goals))]

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

(* get : get the current proof state *)
let get : tac<proofstate> =
    mk_tac (fun p -> Success (p, p))

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
        then dump_proofstate ps ("TACTING FAILING: " ^ msg);
        Failed (msg, ps)
    )

let fail1 msg x     = fail (BU.format1 msg x)
let fail2 msg x y   = fail (BU.format2 msg x y)
let fail3 msg x y z = fail (BU.format3 msg x y z)

let trytac (t : tac<'a>) : tac<option<'a>> =
    mk_tac (fun ps ->
            let tx = UF.new_transaction () in
            match run t ps with
            | Success (a, q) ->
                UF.commit tx;
                Success (Some a, q)
            | Failed (_, _) ->
                UF.rollback tx;
                Success (None, ps)
           )

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

let do_unify (env : env) (t1 : term) (t2 : term) : bool =
    try Rel.teq_nosmt env t1 t2
    with | _ -> false

let trysolve (goal : goal) (solution : term) : bool =
    do_unify goal.context solution goal.witness

let dismiss : tac<unit> =
    bind get (fun p ->
    set ({p with goals=List.tl p.goals}))

let solve (goal : goal) (solution : term) : tac<unit> =
    if trysolve goal solution
    then dismiss
    else fail (BU.format3 "%s does not solve %s : %s"
              (N.term_to_string goal.context solution)
              (N.term_to_string goal.context goal.witness)
              (N.term_to_string goal.context goal.goal_ty))

let dismiss_all : tac<unit> =
    bind get (fun p ->
    set ({p with goals=[]}))

let check_valid_goal g =
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
    if not (aux b env)
    then Err.warn g.goal_ty.pos
             (BU.format1 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                         (goal_to_string g))

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
    bind dismiss (fun _ ->
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


let cur_goal : tac<goal> =
    bind get (fun p ->
    match p.goals with
    | [] -> fail "No more goals (1)"
    | hd::tl -> ret hd)

let mk_irrelevant_goal (reason:string) (env:env) (phi:typ) opts : tac<goal> =
    let typ = U.mk_squash phi in
    bind (new_uvar reason env typ) (fun u ->
    let goal = { context = env; witness = u; goal_ty = typ; opts = opts; is_guard = false } in
    ret goal)

let __tc (e : env) (t : term) : tac<(term * typ * guard_t)> =
    bind get (fun ps ->
    try ret (ps.main_context.type_of e t) with e -> fail "not typeable")

let must_trivial (e : env) (g : guard_t) : tac<unit> =
    try if not (Rel.is_trivial <| Rel.discharge_guard_no_smt e g)
        then fail "got non-trivial guard"
        else ret ()
    with
    | _ -> fail "got non-trivial guard"

let tc (t : term) : tac<typ> = wrap_err "tc" <|
    bind cur_goal (fun goal ->
    bind (__tc goal.context t) (fun (t, typ, guard) ->
    bind (must_trivial goal.context guard) (fun _ ->
    ret typ
    )))

let add_irrelevant_goal reason env phi opts : tac<unit> =
    bind (mk_irrelevant_goal reason env phi opts) (fun goal ->
    add_goals [goal])

let istrivial (e:env) (t:term) : bool =
    let steps = [N.Reify; N.UnfoldUntil Delta_constant; N.Primops; N.Simplify; N.UnfoldTac; N.Unmeta] in
    let t = normalize steps e t in
    is_true t

let trivial : tac<unit> =
    bind cur_goal (fun goal ->
    if istrivial goal.context goal.goal_ty
    then solve goal U.exp_unit
    else fail1 "Not a trivial goal: %s" (N.term_to_string goal.context goal.goal_ty)
    )

let add_goal_from_guard (reason:string) (e:env) (g : guard_t) opts : tac<unit> =
    match (Rel.simplify_guard e g).guard_f with
    | TcComm.Trivial -> ret ()
    | TcComm.NonTrivial f ->
        if istrivial e f then ret () else
        bind (mk_irrelevant_goal reason e f opts) (fun goal ->
        let goal = { goal with is_guard = true } in
        push_goals [goal])

let smt : tac<unit> =
    bind cur_goal (fun g ->
    if is_irrelevant g then
        bind dismiss (fun _ -> add_smt_goals [g])
    else
        fail1 "goal is not irrelevant: cannot dispatch to smt (%s)" (N.term_to_string g.context g.goal_ty)
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

let intro : tac<binder> =
    bind cur_goal (fun goal ->
    match U.arrow_one goal.goal_ty with
    | Some (b, c) ->
        if not (U.is_total_comp c)
        then fail "Codomain is effectful"
        else let env' = Env.push_binders goal.context [b] in
             let typ' = comp_to_typ c in
             bind (new_uvar "intro" env' typ') (fun u ->
             if trysolve goal (U.abs [b] u None)
             then bind (replace_cur ({ goal with context = env';
                                                 goal_ty = bnorm env' typ';
                                                 witness = bnorm env' u})) (fun _ ->
                  ret b)
             else fail "intro: unification failed"
             )
    | None ->
        fail1 "intro: goal is not an arrow (%s)" (N.term_to_string goal.context goal.goal_ty)
    )

// TODO: missing: precedes clause, and somehow disabling fixpoints only as needed
let intro_rec : tac<(binder * binder)> =
    bind cur_goal (fun goal ->
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
             let lb = U.mk_letbinding (Inl bv) [] goal.goal_ty PC.effect_Tot_lid (U.abs [b] u None) in
             let body = S.bv_to_name bv in
             let lbs, body = SS.close_let_rec [lb] body in
             let tm = mk (Tm_let ((true, lbs), body)) None goal.witness.pos in
             let res = trysolve goal tm in
             if res
             then bind (replace_cur ({ goal with context = env';
                                                 goal_ty = bnorm env' (comp_to_typ c);
                                                 witness = bnorm env' u})) (fun _ ->
                  ret (S.mk_binder bv, b))
             else fail "intro_rec: unification failed"
             )
    | None ->
        fail1 "intro_rec: goal is not an arrow (%s)" (N.term_to_string goal.context goal.goal_ty)
    )

let norm (s : list<EMB.norm_step>) : tac<unit> =
    bind cur_goal (fun goal ->
    // Translate to actual normalizer steps
    let steps = [N.Reify; N.UnfoldTac]@(N.tr_norm_steps s) in
    let w = normalize steps goal.context goal.witness in
    let t = normalize steps goal.context goal.goal_ty in
    replace_cur ({goal with goal_ty = t; witness = w})
    )

let norm_term_env (e : env) (s : list<EMB.norm_step>) (t : term) : tac<term> = wrap_err "norm_term" <|
    bind get (fun ps ->
    bind (__tc e t) (fun (t, _, guard) ->
    Rel.force_trivial_guard e guard;
    let steps = [N.Reify; N.UnfoldTac]@(N.tr_norm_steps s) in
    let t = normalize steps ps.main_context t in
    ret t
    ))

let __exact force_guard (t:term) : tac<unit> =
    bind cur_goal (fun goal ->
    bind (__tc goal.context t) (fun (t, typ, guard) ->
    bind (if force_guard
          then must_trivial goal.context guard
          else add_goal_from_guard "__exact typing" goal.context guard goal.opts
          ) (fun _ ->
    if do_unify goal.context typ goal.goal_ty
    then solve goal t
    else fail3 "%s : %s does not exactly solve the goal %s"
                    (N.term_to_string goal.context t)
                    (N.term_to_string goal.context (bnorm goal.context typ))
                    (N.term_to_string goal.context goal.goal_ty))))

let exact (tm:term) : tac<unit> = wrap_err "exact" <|
    mlog (fun () -> BU.print1 "exact: tm = %s\n" (Print.term_to_string tm)) (fun _ ->
    focus (__exact true tm)
    )

let exact_guard (tm:term) : tac<unit> = wrap_err "exact_guard" <|
    mlog (fun () -> BU.print1 "exact_guard: tm = %s\n" (Print.term_to_string tm)) (fun _ ->
    focus (__exact false tm)
    )

let uvar_free_in_goal (u:uvar) (g:goal) =
    if g.is_guard then false else
    let free_uvars = List.map fst (BU.set_elements (SF.uvars g.goal_ty)) in
    List.existsML (UF.equiv u) free_uvars

let uvar_free (u:uvar) (ps:proofstate) : bool =
    List.existsML (uvar_free_in_goal u) ps.goals

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
let rec __apply (uopt:bool) (tm:term) (typ:typ) : tac<unit> =
    bind cur_goal (fun goal ->
    bind (trytac (__exact true tm)) (fun r ->
    match r with
    | Some r -> ret r // if tm is a solution, we're done
    | None ->
        // exact failed, try to instantiate more arguments
        match U.arrow_one typ with
        | None -> raise NoUnif
        | Some ((bv, aq), c) ->
            mlog (fun () ->
                BU.print1 "__apply: pushing binder %s\n" (Print.binder_to_string (bv, aq))) (fun _ ->
            if not (U.is_total_comp c) then fail "apply: not total codomain" else
            bind (new_uvar "apply" goal.context bv.sort) (fun u ->
            (* BU.print1 "__apply: witness is %s\n" (Print.term_to_string u); *)
            let tm' = mk_Tm_app tm [(u, aq)] None goal.context.range in
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
            )))))

// The exception is thrown only when the tactic runs, not when it's defined,
// so we need to do this to catch it
let try_unif (t : tac<'a>) (t' : tac<'a>) : tac<'a> =
    mk_tac (fun ps ->
        try run t ps
        with NoUnif -> run t' ps)

let apply (uopt:bool) (tm:term) : tac<unit> = wrap_err "apply" <|
    mlog (fun () -> BU.print1 "apply: tm = %s\n" (Print.term_to_string tm)) (fun _ ->
    bind cur_goal (fun goal ->
    bind (__tc goal.context tm) (fun (tm, typ, guard) ->
    // Focus helps keep the goal order
    try_unif (focus (bind (__apply uopt tm typ) (fun _ -> add_goal_from_guard "apply guard" goal.context guard goal.opts)))
             (fail3 "Cannot instantiate %s (of type %s) to match goal (%s)"
                            (N.term_to_string goal.context tm)
                            (N.term_to_string goal.context typ)
                            (N.term_to_string goal.context goal.goal_ty))
    )))

let apply_lemma (tm:term) : tac<unit> = wrap_err "apply_lemma" <| focus(
    mlog (fun () -> BU.print1 "apply_lemma: tm = %s\n" (Print.term_to_string tm)) (fun _ ->
    let is_unit_t t = match (SS.compress t).n with
    | Tm_fvar fv when S.fv_eq_lid fv PC.unit_lid -> true
    | _ -> false
    in
    bind cur_goal (fun goal ->
    bind (__tc goal.context tm) (fun (tm, t, guard) ->
    let bs, comp = U.arrow_formals_comp t in
    if not (U.is_lemma_comp comp) then fail "not a lemma" else
    let uvs, implicits, subst =
       List.fold_left (fun (uvs, guard, subst) (b, aq) ->
               let b_t = SS.subst subst b.sort in
               if is_unit_t b_t
               then
                   // Simplification: if the argument is simply unit, then don't ask for it
                   (U.exp_unit, aq)::uvs, guard, S.NT(b, U.exp_unit)::subst
               else
                   let u, _, g_u = FStar.TypeChecker.Util.new_implicit_var "apply_lemma" goal.goal_ty.pos goal.context b_t in
                   (u, aq)::uvs,
                   FStar.TypeChecker.Rel.conj_guard guard g_u,
                   S.NT(b, u)::subst
               )
       ([], guard, [])
       bs
    in
    let uvs = List.rev uvs in
    let comp = SS.subst_comp subst comp in
    let pre, post = match (U.comp_to_comp_typ comp).effect_args with
                    | pre::post::_ -> fst pre, fst post
                    | _ -> failwith "apply_lemma: impossible: not a lemma"
    in
    // Lemma post is thunked
    let post = U.mk_app post [S.as_arg U.exp_unit] in
    if not (do_unify goal.context (U.mk_squash post) goal.goal_ty)
    then fail3 "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                            (N.term_to_string goal.context tm)
                            (N.term_to_string goal.context (U.mk_squash post))
                            (N.term_to_string goal.context goal.goal_ty)
    else
        let solution = N.normalize [N.Beta] goal.context (S.mk_Tm_app tm uvs None goal.context.range) in
        bind (add_implicits implicits.implicits) (fun _ ->
        let implicits = implicits.implicits |> List.filter (fun (_, _, _, tm, _, _) ->
             let hd, _ = U.head_and_args tm in
             match (SS.compress hd).n with
             | Tm_uvar _ -> true //still unresolved
             | _ -> false) in
        bind (solve goal solution) (fun _ ->
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
        let sub_goals =
             implicits |> List.map (fun (_msg, _env, _uvar, term, typ, _) ->
                     { goal with
                      witness = bnorm goal.context term;
                      goal_ty = bnorm goal.context typ })
        in
        // Optimization: if a uvar appears in a later goal, don't ask for it, since
        // it will be instantiated later. TODO: maybe keep and check later?
        let rec filter' (f : 'a -> list<'a> -> bool) (xs : list<'a>) : list<'a> =
             match xs with
             | [] -> []
             | x::xs -> if f x xs then x::(filter' f xs) else filter' f xs
        in
        let sub_goals = filter' (fun g goals -> not (checkone g.witness goals)) sub_goals in
        bind (add_goal_from_guard "apply_lemma guard" goal.context guard goal.opts) (fun _ ->
        bind (if not (istrivial goal.context (U.mk_squash pre))
              then add_irrelevant_goal "apply_lemma precondition" goal.context pre goal.opts
              else ret ()) (fun _ ->
        add_goals sub_goals))))))))

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
    bind cur_goal (fun goal ->
    let bv, _ = h in
    mlog (fun _ -> BU.print2 "+++Rewrite %s : %s\n" (Print.bv_to_string bv) (Print.term_to_string bv.sort)) (fun _ ->
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
    bind cur_goal (fun goal ->
    let bv, _ = b in
    let bv' = freshen_bv ({ bv with ppname = mk_ident (s, bv.ppname.idRange) }) in
    let s = [NT (bv, S.bv_to_name bv')] in
    match subst_goal bv bv' s goal with
    | None -> fail "rename_to: binder not found in environment"
    | Some goal -> replace_cur goal)

let binder_retype (b : binder) : tac<unit> =
    bind cur_goal (fun goal ->
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
        bind dismiss (fun _ ->
        bind (add_goals [{goal with context = env';
                                    witness = SS.subst s goal.witness;
                                    goal_ty = SS.subst s goal.goal_ty }]) (fun _ ->
              add_irrelevant_goal "binder_retype equation" e0
                  (U.mk_eq2 (U_succ u) ty bv.sort t') goal.opts)))
         end)

let norm_binder_type (s : list<EMB.norm_step>) (b : binder) : tac<unit> =
    bind cur_goal (fun goal ->
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

let revert : tac<unit> =
    bind cur_goal (fun goal ->
    match Env.pop_bv goal.context with
    | None -> fail "Cannot revert; empty context"
    | Some (x, env') ->
        let typ' = U.arrow [(x, None)] (mk_Total goal.goal_ty) in
        let w' = U.abs [(x, None)] goal.witness None in
        replace_cur ({ goal with context = env'; witness = w'; goal_ty = typ' })
    )

let revert_hd (x : name) : tac<unit> =
    bind cur_goal (fun goal ->
    match Env.pop_bv goal.context with
    | None -> fail "Cannot revert_hd; empty context"
    | Some (y, env') ->
        if not (S.bv_eq x y)
        then fail2 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                              (Print.bv_to_string x)
                              (Print.bv_to_string y)
        else revert)

let clear_top : tac<unit> =
    bind cur_goal (fun goal ->
    match Env.pop_bv goal.context with
    | None -> fail "Cannot clear; empty context"
    | Some (x, env') ->
        let fns_ty = FStar.Syntax.Free.names goal.goal_ty in
        (* let fns_tm = FStar.Syntax.Free.names goal.witness in *)
        if Util.set_mem x fns_ty (* || Util.set_mem x fns_tm *)
        then fail "Cannot clear; variable appears in goal"
        else bind (new_uvar "clear_top" env' goal.goal_ty) (fun u ->
             if not (trysolve goal u)
             then fail "clear: unification failed"
             else let new_goal = {goal with context = env'; witness = bnorm env' u} in
                  bind dismiss (fun _ ->
                  add_goals [new_goal])))

let rec clear (b : binder) : tac<unit> =
    bind cur_goal (fun goal ->
    match Env.pop_bv goal.context with
    | None -> fail "Cannot clear; empty context"
    | Some (b', env') ->
        if S.bv_eq (fst b) b'
        then clear_top
        else bind revert (fun _ ->
             bind (clear b) (fun _ ->
             bind intro (fun _ ->
             ret ()))))

let prune (s:string) : tac<unit> =
    bind cur_goal (fun g ->
    let ctx = g.context in
    let ctx' = Env.rem_proof_ns ctx (path_of_text s) in
    let g' = { g with context = ctx' } in
    bind dismiss (fun _ -> add_goals [g']))

let addns (s:string) : tac<unit> =
    bind cur_goal (fun g ->
    let ctx = g.context in
    let ctx' = Env.add_proof_ns ctx (path_of_text s) in
    let g' = { g with context = ctx' } in
    bind dismiss (fun _ -> add_goals [g']))

let rec mapM (f : 'a -> tac<'b>) (l : list<'a>) : tac<list<'b>> =
    match l with
    | [] -> ret []
    | x::xs ->
        bind (f x) (fun y ->
        bind (mapM f xs) (fun ys ->
        ret (y::ys)))

let rec tac_fold_env (d : direction) (f : env -> term -> tac<term>) (env : env) (t : term) : tac<term> =
    let tn = (SS.compress t).n in
    bind (if d = TopDown
          then f env ({ t with n = tn })
          else ret t) (fun t ->
    let tn = match (SS.compress t).n with
             | Tm_app (hd, args) ->
                  let ff = tac_fold_env d f env in
                  bind (ff hd) (fun hd ->
                  let fa (a,q) = bind (ff a) (fun a -> (ret (a,q))) in
                  bind (mapM fa args) (fun args ->
                  ret (Tm_app (hd, args))))
             | Tm_abs (bs, t, k) ->
                 let bs, t' = SS.open_term bs t in
                 bind (tac_fold_env d f (Env.push_binders env bs) t') (fun t'' ->
                 ret (Tm_abs (SS.close_binders bs, SS.close bs t'', k)))
             | Tm_arrow (bs, k) -> ret tn //TODO
             | _ -> ret tn in
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
                // Try to get rid of all the unification lambdas
                let ut = N.reduce_uvar_solutions env ut in
                log ps (fun () ->
                    BU.print2 "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                (Print.term_to_string t)
                                (Print.term_to_string ut));
                ret ut))
          ))
       in
       bind (trytac rewrite_eq) (fun x ->
       match x with
       | None -> ret t
       | Some x -> ret x)

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

let trefl : tac<unit> =
    bind cur_goal (fun g ->
    match U.un_squash g.goal_ty with
    | Some t ->
        begin
        let hd, args = U.head_and_args' t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [_; (l, _); (r, _)] when S.fv_eq_lid fv PC.eq2_lid ->
            if not (do_unify g.context l r)
            then fail2 "trefl: not a trivial equality (%s vs %s)" (N.term_to_string g.context l) (N.term_to_string g.context r)
            else solve g U.exp_unit
        | hd, _ ->
            fail1 "trefl: not an equality (%s)" (N.term_to_string g.context t)
        end
     | None ->
        fail "not an irrelevant goal")

let dup : tac<unit> =
    bind cur_goal (fun g ->
    bind (new_uvar "dup" g.context g.goal_ty) (fun u ->
    let g' = { g with witness = u } in
    bind dismiss (fun _ ->
    bind (add_irrelevant_goal "dup equation" g.context
               (U.mk_eq2 (TcTerm.universe_of g.context g.goal_ty) g.goal_ty u g.witness) g.opts) (fun _ ->
    bind (add_goals [g']) (fun _ ->
    ret ())))))

let flip : tac<unit> =
    bind get (fun ps ->
    match ps.goals with
    | g1::g2::gs -> set ({ps with goals=g2::g1::gs})
    | _ -> fail "flip: less than 2 goals"
    )

let later : tac<unit> =
    bind get (fun ps ->
    match ps.goals with
    | [] -> ret ()
    | g::gs -> set ({ps with goals=gs@[g]})
    )

let qed : tac<unit> =
    bind get (fun ps ->
    match ps.goals with
    | [] -> ret ()
    | _ -> fail "Not done!"
    )

let cases (t : term) : tac<(term * term)> = wrap_err "cases" <|
    bind cur_goal (fun g ->
    bind (__tc g.context t) (fun (t, typ, guard) ->
    let hd, args = U.head_and_args typ in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [(p, _); (q, _)] when S.fv_eq_lid fv PC.or_lid ->
        let v_p = S.new_bv None p in
        let v_q = S.new_bv None q in
        let g1 = {g with context = Env.push_bv g.context v_p } in
        let g2 = {g with context = Env.push_bv g.context v_q } in
        bind dismiss (fun _ ->
        bind (add_goals [g1; g2]) (fun _ ->
        ret (S.bv_to_name v_p, S.bv_to_name v_q)))
    | _ ->
        fail1 "Not a disjunction: %s" (N.term_to_string g.context typ)))

let set_options (s : string) : tac<unit> =
    bind cur_goal (fun g ->
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

let top_env     : tac<env>  = bind get (fun ps -> ret <| ps.main_context)
let cur_env     : tac<env>  = bind cur_goal (fun g -> ret <| g.context)
let cur_goal'   : tac<term> = bind cur_goal (fun g -> ret <| g.goal_ty)
let cur_witness : tac<term> = bind cur_goal (fun g -> ret <| g.witness)

let unquote (ty : term) (tm : term) : tac<term> = wrap_err "unquote" <|
    bind cur_goal (fun goal ->
    let env = Env.set_expected_typ goal.context ty in
    bind (__tc env tm) (fun (tm, typ, guard) ->
    Rel.force_trivial_guard env guard;
    ret tm))

let uvar_env (env : env) (ty : option<typ>) : tac<term> =
    // If no type was given, add an uvar for it too!
    bind (match ty with
    | Some ty -> ret ty
    | None -> new_uvar "uvar_env.2" env (fst <| U.type_u ())) (fun typ ->
    bind (new_uvar "uvar_env" env typ) (fun t ->
    ret t))

let unshelve (t : term) : tac<unit> = wrap_err "unshelve" <|
    bind cur_goal (fun goal ->
    bind (__tc goal.context t) (fun (t, typ, guard) ->
    bind (must_trivial goal.context guard) (fun _ ->
    add_goals [{ goal with witness  = bnorm goal.context t;
                           goal_ty  = bnorm goal.context typ;
                           is_guard = false; }])))

let unify (t1 : term) (t2 : term) : tac<bool> =
    bind get (fun ps ->
    ret (do_unify ps.main_context t1 t2)
    )

let launch_process (prog : string) (args : string) (input : string) : tac<string> =
    // The `bind idtac` thunks the tactic
    bind idtac (fun () ->
    if Options.unsafe_tactic_exec () then
        let s = BU.launch_process true "tactic_launch" prog args input (fun _ _ -> false) in
        ret s
    else
        fail "launch_process: will not run anything unless --unsafe_tactic_exec is provided"
    )

let goal_of_goal_ty env typ : goal * guard_t =
    let u, _, g_u = TcUtil.new_implicit_var "proofstate_of_goal_ty" typ.pos env typ in
    let g =  {
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
    }
    in
    (ps, g.witness)

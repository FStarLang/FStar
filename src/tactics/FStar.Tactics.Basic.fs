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

type name = bv
type env = Env.env
type implicits = Env.implicits

// Beta reduce
let normalize s e t = N.normalize_with_primitive_steps FStar.Reflection.Interpreter.reflection_primops s e t
let bnorm e t = normalize [] e t

(*
   f: x:int -> P
   ==================
      P
 *)
//A goal is typically of the form
//    G |- ?u : t
// where context = G
//       witness = ?u, although, more generally, witness is a partial solution and can be any term
//       goal_ty = t
type goal = {
    context : env;
    witness : term;
    goal_ty : typ;
    opts    : FStar.Options.optionstate; // option state for this particular goal
}

type proofstate = {
    main_context : env;          //the shared top-level context for all goals
    main_goal    : goal;         //this is read only; it helps keep track of the goal we started working on initially
    all_implicits: implicits ;   //all the implicits currently open, partially resolved (unclear why we really need this)
    goals        : list<goal>;   //all the goals remaining to be solved
    smt_goals    : list<goal>;   //goals that have been deferred to SMT
}

type result<'a> =
    | Success of 'a * proofstate
    | Failed  of string    //error message
              * proofstate //the proofstate at time of failure

(* An exception, typically used only to simplify local data flow,
                 although, when not handled, it signifies a fatal error
                           in the tactic engine
*)
exception TacFailure of string

(* The main monad for tactics.
 * A record, so we can keep it somewhat encapsulated and
 * can more easily add things to it if need be.
 *)
type tac<'a> = {
    tac_f : proofstate -> result<'a>;
}

let mk_tac (f : proofstate -> result<'a>) : tac<'a> =
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
    Util.format3 "%s |- %s : %s" g_binders (Print.term_to_string g.witness) (Print.term_to_string g.goal_ty)

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

let ps_to_string (msg, ps) = format5 "State dump (%s):\nACTIVE goals (%s):\n%s\nSMT goals (%s):\n%s"
                msg (string_of_int (List.length ps.goals)) (String.concat "\n" (List.map goal_to_string ps.goals))
                (string_of_int (List.length ps.smt_goals)) (String.concat "\n" (List.map goal_to_string ps.smt_goals))
let goal_to_json g =
    let g_binders = Env.all_binders g.context |> Print.binders_to_json in
    JsonAssoc [("hyps", g_binders);
               ("goal", JsonAssoc [("witness", JsonStr (Print.term_to_string g.witness));
                                   ("type", JsonStr (Print.term_to_string g.goal_ty))])]

let ps_to_json (msg, ps) =
    JsonAssoc [("label", JsonStr msg);
               ("goals", JsonList (List.map goal_to_json ps.goals));
               ("smt-goals", JsonList (List.map goal_to_json ps.smt_goals))]

let dump_proofstate ps msg =
    Options.with_saved_options (fun () ->
        Options.set_option "print_effect_args" (Options.Bool true);
        print_generic "proof-state" ps_to_string ps_to_json (msg, ps))
    // tacprint "";
    // tacprint1 "State dump (%s):" msg;
    // tacprint1 "ACTIVE goals (%s):" (string_of_int (List.length ps.goals));
    // List.iter (dump_goal ps) ps.goals;
    // tacprint1 "SMT goals (%s):" (string_of_int (List.length ps.smt_goals));
    // List.iter (dump_goal ps) ps.smt_goals;
    // ()

let print_proof_state1 (msg:string) : tac<unit> =
    mk_tac (fun p -> dump_cur p msg;
                     Success ((), p))

let print_proof_state (msg:string) : tac<unit> =
    mk_tac (fun p -> dump_proofstate p msg;
                     Success ((), p))

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

let mlog f : tac<unit> =
    bind get (fun ps -> log ps f; ret ())

//val fail : string -> tac<'a>
let fail msg =
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

////////////////////////////////////////////////////////////////////
(* Some TRUSTED internal utilities *)

(* set : set the current proof state; shouldn't be exposed externally *)
let set (p:proofstate) : tac<unit> =
    mk_tac (fun _ -> Success ((), p))

let solve goal solution =
    if Rel.teq_nosmt goal.context goal.witness solution
    then ()
    else raise (TacFailure(BU.format3 "%s does not solve %s : %s"
                          (Print.term_to_string solution)
                          (Print.term_to_string goal.witness)
                          (Print.term_to_string goal.goal_ty)))

let dismiss : tac<unit> =
    bind get (fun p ->
    set ({p with goals=List.tl p.goals}))

let dismiss_all : tac<unit> =
    bind get (fun p ->
    set ({p with goals=[]}))

let add_goals (gs:list<goal>) : tac<unit> =
    bind get (fun p ->
    set ({p with goals=gs@p.goals}))

let add_smt_goals (gs:list<goal>) : tac<unit> =
    bind get (fun p ->
    set ({p with smt_goals=gs@p.smt_goals}))

let push_goals (gs:list<goal>) : tac<unit> =
    bind get (fun p ->
    set ({p with goals=p.goals@gs}))

let push_smt_goals (gs:list<goal>) : tac<unit> =
    bind get (fun p ->
    set ({p with smt_goals=p.smt_goals@gs}))

let replace_cur (g:goal) : tac<unit> =
    bind dismiss (fun _ ->
    add_goals [g])

let add_implicits (i:implicits) : tac<unit> =
    bind get (fun p ->
    set ({p with all_implicits=i@p.all_implicits}))

let new_uvar (env:env) (typ:typ) : tac<term> =
    let u, _, g_u = TcUtil.new_implicit_var "tactics.new_uvar" typ.pos env typ in
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

let mk_irrelevant_goal (env:env) (phi:typ) opts : tac<goal> =
    let typ = U.mk_squash phi in
    bind (new_uvar env typ) (fun u ->
    let goal = { context = env; witness = u; goal_ty = typ; opts = opts } in
    ret goal)

let add_irrelevant_goal env phi opts : tac<unit> =
    bind (mk_irrelevant_goal env phi opts) (fun goal ->
    add_goals [goal])

let push_irrelevant_goal env phi opts : tac<unit> =
    bind (mk_irrelevant_goal env phi opts) (fun goal ->
    push_goals [goal])

let istrivial (e:env) (t:term) : bool =
    let steps = [N.Reify; N.UnfoldUntil Delta_constant; N.Primops; N.Simplify; N.UnfoldTac] in
    let t = normalize steps e t in
    is_true t

let trivial : tac<unit> =
    bind cur_goal (fun goal ->
    if istrivial goal.context goal.goal_ty
    then (solve goal U.exp_unit; dismiss)
    else fail1 "Not a trivial goal: %s" (Print.term_to_string goal.goal_ty)
    )

let add_goal_from_guard (e:env) (g : guard_t) opts : tac<unit> =
    match (Rel.simplify_guard e g).guard_f with
    | TcComm.Trivial -> ret ()
    | TcComm.NonTrivial f ->
        push_irrelevant_goal e f opts

let smt : tac<unit> =
    bind cur_goal (fun g ->
    if is_irrelevant g then
        bind dismiss (fun _ -> add_smt_goals [g])
    else
        fail1 "goal is not irrelevant: cannot dispatch to smt (%s)" (Print.term_to_string g.goal_ty)
    )

let divide (n:int) (l : tac<'a>) (r : tac<'b>) : tac<('a * 'b)> =
    bind get (fun p ->
    bind (try ret (List.splitAt n p.goals) with | _ -> fail "divide: not enough goals") (fun (lgs, rgs) ->
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
    bind (divide 1 f idtac) (fun (a, ()) -> ret a)

(* Applies t to each of the current goals
      fails if t fails on any of the goals
      collects each result in the output list *)
let rec map (tau:tac<'a>): tac<(list<'a>)> =
        bind get (fun p ->
        match p.goals with
        | [] -> ret []
        | _::_ ->
            bind (divide 1 tau (map tau)) (fun (h,t) -> ret (h :: t))
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
             bind (new_uvar env' typ') (fun u ->
             if Rel.teq_nosmt goal.context goal.witness (U.abs [b] u None)
             then bind (replace_cur ({ goal with context = env';
                                                 goal_ty = bnorm env' typ';
                                                 witness = bnorm env' u})) (fun _ ->
                  ret b)
             else fail "intro: unification failed"
             )
    | None ->
        fail1 "intro: goal is not an arrow (%s)" (Print.term_to_string goal.goal_ty)
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
             bind (new_uvar env' (comp_to_typ c)) (fun u ->
             let lb = U.mk_letbinding (Inl bv) [] goal.goal_ty PC.effect_Tot_lid (U.abs [b] u None) in
             let body = S.bv_to_name bv in
             let lbs, body = SS.close_let_rec [lb] body in
             let tm = mk (Tm_let ((true, lbs), body)) None goal.witness.pos in
             BU.print_string "calling teq_nosmt\n";
             let res = Rel.teq_nosmt goal.context goal.witness tm in
             if res
             then bind (replace_cur ({ goal with context = env';
                                                 goal_ty = bnorm env' (comp_to_typ c);
                                                 witness = bnorm env' u})) (fun _ ->
                  ret (S.mk_binder bv, b))
             else fail "intro_rec: unification failed"
             )
    | None ->
        fail1 "intro_rec: goal is not an arrow (%s)" (Print.term_to_string goal.goal_ty)
    )

let norm (s : list<EMB.norm_step>) : tac<unit> =
    bind cur_goal (fun goal ->
    // Translate to actual normalizer steps
    let steps = [N.Reify; N.UnfoldTac]@(N.tr_norm_steps s) in
    let w = normalize steps goal.context goal.witness in
    let t = normalize steps goal.context goal.goal_ty in
    replace_cur ({goal with goal_ty = t; witness = w})
    )

let norm_term (s : list<EMB.norm_step>) (t : term) : tac<term> =
    bind get (fun ps ->
    let steps = [N.Reify; N.UnfoldTac]@(N.tr_norm_steps s) in
    let t = normalize steps ps.main_context t in
    ret t
    )

let __exact (t:term) : tac<unit> =
    bind cur_goal (fun goal ->
    bind (try ret (goal.context.type_of goal.context t)
          with e -> // printfn "Exception %A" e;
                    fail2 "exact: term is not typeable: %s (%s)" (Print.term_to_string t) (Print.tag_of_term t)) (fun (t, typ, guard) ->
    if not (Rel.is_trivial <| Rel.discharge_guard goal.context guard) then fail "exact: got non-trivial guard" else
    if Rel.teq_nosmt goal.context typ goal.goal_ty
    then let _ = solve goal t in dismiss
    else fail3 "%s : %s does not exactly solve the goal %s"
                    (Print.term_to_string t)
                    (Print.term_to_string (bnorm goal.context typ))
                    (Print.term_to_string goal.goal_ty)))

let exact (t:term) : tac<unit> =
    focus (__exact t)

let exact_lemma (t:term) : tac<unit> =
    bind cur_goal (fun goal ->
    bind (try ret (TcTerm.tc_term goal.context t)
          with e -> // printfn "Exception %A" e;
                    fail2 "exact_lemma: term is not typeable: %s (%s)" (Print.term_to_string t) (Print.tag_of_term t)) (fun (t, lcomp, guard) ->
    let comp = lcomp.comp () in
    if not (U.is_lemma_comp comp) then fail "exact_lemma: not a lemma" else
    if not (Rel.is_trivial guard) then fail "exact: got non-trivial guard" else
    let pre, post = match (U.comp_to_comp_typ comp).effect_args with
                    | pre::post::_ -> fst pre, fst post
                    | _ -> failwith "exact_lemma: impossible: not a lemma"
    in
    if Rel.teq_nosmt goal.context post goal.goal_ty
    then let _ = solve goal t in bind dismiss (fun _ -> add_irrelevant_goal goal.context pre goal.opts)
    else fail3 "%s : %s does not exactly solve the goal %s"
                    (Print.term_to_string t)
                    (Print.term_to_string post)
                    (Print.term_to_string goal.goal_ty)))

let uvar_free_in_goal (u:uvar) (g:goal) =
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
    bind (trytac (__exact tm)) (fun r ->
    match r with
    | Some r -> ret r // if tm is a solution, we're done
    | None ->
        // exact failed, try to instantiate more arguments
        match U.arrow_one typ with
        | None -> raise NoUnif
        | Some ((bv, aq), c) ->
            if not (U.is_total_comp c) then fail "apply: not total codomain" else
            bind (new_uvar goal.context bv.sort) (fun u ->
            let tm' = mk_Tm_app tm [(u, aq)] None goal.context.range in
            let typ' = SS.subst [S.NT (bv, u)] <| comp_to_typ c in
            bind (__apply uopt tm' typ') (fun _ ->
            match (SS.compress (fst (U.head_and_args u))).n with
            | Tm_uvar (uvar, _) ->
                bind get (fun ps ->
                if uopt && uvar_free uvar ps
                then ret ()
                else add_goals [{context = goal.context;
                                 witness = bnorm goal.context u;
                                 goal_ty = bnorm goal.context bv.sort;
                                 opts    = goal.opts; }])
            | _ -> ret ()))))

// The exception is thrown only when the tactic runs, not when it's defined,
// so we need to do this to catch it
let try_unif (t : tac<'a>) (t' : tac<'a>) : tac<'a> =
    mk_tac (fun ps ->
        try run t ps
        with NoUnif -> run t' ps)

let apply (uopt:bool) (tm:term) : tac<unit> =
    bind cur_goal (fun goal ->
    let tm, typ, guard = goal.context.type_of goal.context tm in
    // Focus helps keep the goal order
    try_unif (focus (bind (__apply uopt tm typ) (fun _ -> add_goal_from_guard goal.context guard goal.opts)))
             (fail3 "apply: Cannot instantiate %s (of type %s) to match goal (%s)"
                            (Print.term_to_string tm)
                            (Print.term_to_string typ)
                            (Print.term_to_string goal.goal_ty))
    )

let apply_lemma (tm:term) : tac<unit> = focus(
    let is_unit_t t = match (SS.compress t).n with
    | Tm_fvar fv when S.fv_eq_lid fv PC.unit_lid -> true
    | _ -> false
    in
    bind cur_goal (fun goal ->
    let tm, t, guard = goal.context.type_of goal.context tm in
    let bs, comp = U.arrow_formals_comp t in
    if not (U.is_lemma_comp comp) then fail "apply_lemma: not a lemma" else
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
    match Rel.try_teq false goal.context (U.mk_squash post) goal.goal_ty with
    | None -> fail2 "apply_lemma: does not unify with goal: %s vs %s"
                                 (Print.term_to_string (U.mk_squash post))
                                 (Print.term_to_string goal.goal_ty)
    | Some g ->
        let solution = S.mk_Tm_app tm uvs None goal.context.range in
        let implicits = implicits.implicits |> List.filter (fun (_, _, _, tm, _, _) ->
             let hd, _ = U.head_and_args tm in
             match (SS.compress hd).n with
             | Tm_uvar _ -> true //still unresolved
             | _ -> false) in
        solve goal solution;
        bind (add_implicits implicits) (fun _ ->
        bind dismiss (fun _ ->
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
                     {context = goal.context;
                      witness = bnorm goal.context term;
                      goal_ty = bnorm goal.context typ;
                      opts    = goal.opts; })
        in
        // Optimization: if a uvar appears in a later goal, don't ask for it, since
        // it will be instantiated later. TODO: maybe keep and check later?
        let rec filter' (f : 'a -> list<'a> -> bool) (xs : list<'a>) : list<'a> =
             match xs with
             | [] -> []
             | x::xs -> if f x xs then x::(filter' f xs) else filter' f xs
        in
        let sub_goals = filter' (fun g goals -> not (checkone g.witness goals)) sub_goals in
        bind (add_goal_from_guard goal.context guard goal.opts) (fun _ ->
        bind (add_goal_from_guard goal.context g   goal.opts) (fun _ ->
        bind (add_irrelevant_goal goal.context pre goal.opts) (fun _ ->
        // Try to discharge the precondition, which is often trivial
        bind (trytac trivial) (fun _ ->
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

let rewrite (h:binder) : tac<unit> =
    bind cur_goal (fun goal ->
    bind (mlog <| (fun _ -> BU.print2 "+++Rewrite %s : %s\n" (Print.bv_to_string (fst h)) (Print.term_to_string (fst h).sort))) (fun _ ->
    match destruct_eq (fst <| Env.lookup_bv goal.context (fst h)) with
    | Some  (x, e) ->
    (match (SS.compress x).n with
       | Tm_name x ->
         let goal = {goal with goal_ty=SS.subst [NT(x, e)] goal.goal_ty; witness = SS.subst [NT(x, e)] goal.witness} in
         replace_cur goal
       | _ ->
         fail "Not an equality hypothesis with a variable on the LHS")
    | _ -> fail "Not an equality hypothesis"))

let clear : tac<unit> =
    bind cur_goal (fun goal ->
    match Env.pop_bv goal.context with
    | None -> fail "Cannot clear; empty context"
    | Some (x, env') ->
        let fns_ty = FStar.Syntax.Free.names goal.goal_ty in
//        let fns_tm = FStar.Syntax.Free.names goal.witness in
        if Util.set_mem x fns_ty
        then fail "Cannot clear; variable appears in goal"
        else bind (new_uvar env' goal.goal_ty) (fun u ->
             if not (Rel.teq_nosmt goal.context goal.witness u)
             then fail "clear: unification failed"
             else let new_goal = {goal with context = env'; witness = bnorm env' u} in
                  bind dismiss (fun _ ->
                  add_goals [new_goal])))

let clear_hd (x:name) : tac<unit> =
    bind cur_goal (fun goal ->
    match Env.pop_bv goal.context with
    | None -> fail "Cannot clear_hd; empty context"
    | Some (y, env') ->
        if not (S.bv_eq x y)
        then fail "Cannot clear_hd; head variable mismatch"
        else clear)

let revert : tac<unit> =
    bind cur_goal (fun goal ->
    match Env.pop_bv goal.context with
    | None -> fail "Cannot revert; empty context"
    | Some (x, env') ->
        let typ' = U.arrow [(x, None)] (mk_Total goal.goal_ty) in
        let w' = U.abs [(x, None)] goal.witness None in
        replace_cur ({ goal with context = env'; witness = w'; goal_ty = typ' })
    )

let revert_hd (x:name) : tac<unit> =
    bind cur_goal (fun goal ->
    match Env.pop_bv goal.context with
    | None -> fail "Cannot revert_hd; empty context"
    | Some (y, env') ->
        if not (S.bv_eq x y)
        then fail2 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                              (Print.bv_to_string x)
                              (Print.bv_to_string y)
        else revert)

let rec revert_all_hd (xs:list<name>) : tac<unit> =
    match xs with
    | [] -> ret ()
    | x::xs ->
        bind (revert_all_hd xs) (fun _ ->
        revert_hd x)

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

let rec tac_bottom_fold_env (f : env -> term -> tac<term>) (env : env) (t : term) : tac<term> =
    let tn = (SS.compress t).n in
    let tn = match tn with
             | Tm_app (hd, args) ->
                  let ff = tac_bottom_fold_env f env in
                  bind (ff hd) (fun hd ->
                  let fa (a,q) = bind (ff a) (fun a -> (ret (a,q))) in
                  bind (mapM fa args) (fun args ->
                  ret (Tm_app (hd, args))))
             | Tm_abs (bs, t, k) ->
                 let bs, t' = SS.open_term bs t in
                 bind (tac_bottom_fold_env f (Env.push_binders env bs) t') (fun t'' ->
                 ret (Tm_abs (SS.close_binders bs, SS.close bs t'', k)))
             | Tm_arrow (bs, k) -> ret tn //TODO
             | _ -> ret tn in
    bind tn (fun tn ->
    f env ({ t with n = tn }))

(*
 * Allows for replacement of individual subterms in the goal, asking the user to provide
 * a proof of the equality. Users are presented with goals of the form `t == ?u` for `t`
 * subterms of the current goal and `?u` a fresh unification variable. The users then
 * calls apply_lemma to fully instantiate `u` and provide a proof of the equality.
 * If all that is successful, the term is rewritten.
 *)
let pointwise_rec (ps : proofstate) (tau : tac<unit>) opts (env : Env.env) (t : term) : tac<term> =
    let t, lcomp, g = TcTerm.tc_term env t in
    if not (U.is_total_lcomp lcomp) || not (Rel.is_trivial g) then
        ret t // Don't do anything for possibly impure terms
    else
        let typ = lcomp.res_typ in
        bind (new_uvar env typ) (fun ut ->
        log ps (fun () ->
            BU.print2 "Pointwise_rec: making equality %s = %s\n" (Print.term_to_string t)
                                                                 (Print.term_to_string ut));
        bind (add_irrelevant_goal env (U.mk_eq2 (TcTerm.universe_of env typ) typ t ut) opts) (fun _ ->
        focus (
            bind tau (fun _ ->
            // Try to get rid of all the unification lambdas
            let ut = N.reduce_uvar_solutions env ut in
            ret ut))
        ))

let pointwise (tau:tac<unit>) : tac<unit> =
    bind get (fun ps ->
    let g, gs = match ps.goals with
                | g::gs -> g, gs
                | [] -> failwith "Pointwise: no goals"
    in
    let gt = g.goal_ty in
    log ps (fun () ->
        BU.print1 "Pointwise starting with %s\n" (Print.term_to_string gt));
    bind dismiss_all (fun _ ->
    bind (tac_bottom_fold_env (pointwise_rec ps tau g.opts) g.context gt) (fun gt' ->
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
            if not (Rel.teq_nosmt g.context l r)
            then fail2 "trefl: not a trivial equality (%s vs %s)" (Print.term_to_string l) (Print.term_to_string r)
            else
            begin
                solve g U.exp_unit;
                dismiss
            end
        | hd, _ ->
            fail1 "trefl: not an equality (%s)" (Print.term_to_string t)
        end
     | None ->
        fail "not an irrelevant goal")

let dup : tac<unit> =
    bind cur_goal (fun g ->
    bind (new_uvar g.context g.goal_ty) (fun u ->
    let g' = { g with witness = u } in
    bind dismiss (fun _ ->
    bind (add_irrelevant_goal g.context (U.mk_eq2 (TcTerm.universe_of g.context g.goal_ty) g.goal_ty u g.witness) g.opts) (fun _ ->
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

let cases (t : term) : tac<(term * term)> =
    bind cur_goal (fun g ->
    let t, typ, guard = g.context.type_of g.context t in
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
        fail1 "Not a disjunction: %s" (Print.term_to_string typ))

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

let cur_env     : tac<env>  = bind cur_goal (fun g -> ret <| g.context)
let cur_goal'   : tac<term> = bind cur_goal (fun g -> ret <| g.goal_ty)
let cur_witness : tac<term> = bind cur_goal (fun g -> ret <| g.witness)

let unquote (ty : term) (tm : term) : tac<term> =
    bind cur_goal (fun goal ->
    let env = Env.set_expected_typ goal.context ty in
    let tm, typ, guard = goal.context.type_of env tm in
    Rel.force_trivial_guard env guard;
    ret tm)

let uvar_env (env : env) (ty : option<typ>) : tac<term> =
    // If no type was given, add an uvar for it too!
    bind (match ty with
    | Some ty -> ret ty
    | None -> new_uvar env (fst <| U.type_u ())) (fun typ ->
    bind (new_uvar env typ) (fun t ->
    ret t))

let unify (t1 : term) (t2 : term) : tac<bool> =
    bind get (fun ps ->
    ret (Rel.teq_nosmt ps.main_context t1 t2)
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
    }
    in
    (ps, g.witness)

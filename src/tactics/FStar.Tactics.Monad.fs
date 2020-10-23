#light "off"
module FStar.Tactics.Monad

open FStar
open FStar.All
open FStar.Syntax.Syntax
open FStar.TypeChecker.Common
open FStar.TypeChecker.Env
open FStar.Tactics.Types
open FStar.Tactics.Result
open FStar.Tactics.Printing
open FStar.Tactics.Common

module O       = FStar.Options
module BU      = FStar.Util
module Err     = FStar.Errors
module S       = FStar.Syntax.Syntax
module U       = FStar.Syntax.Util
module UF      = FStar.Syntax.Unionfind
module Print   = FStar.Syntax.Print
module Env     = FStar.TypeChecker.Env
module Rel     = FStar.TypeChecker.Rel

(*
 * A record, so we can keep it somewhat encapsulated and
 * can more easily add things to it if need be.
 *)
type tac<'a> = {
    tac_f : proofstate -> __result<'a>;
}

let mk_tac (f : proofstate -> __result<'a>) : tac<'a> =
    { tac_f = f }

let run (t:tac<'a>) (ps:proofstate) : __result<'a> =
    t.tac_f ps

let run_safe t ps =
    if Options.tactics_failhard ()
    then run t ps
    else try run t ps
    with | Errors.Err (_, msg)
         | Errors.Error (_, msg, _) -> Failed (TacticFailure msg, ps)
         | e -> Failed (e, ps)

let ret (x:'a) : tac<'a> =
    mk_tac (fun ps -> Success (x, ps))

let bind (t1:tac<'a>) (t2:'a -> tac<'b>) : tac<'b> =
    mk_tac (fun ps ->
            match run t1 ps with
            | Success (a, q)  -> run (t2 a) q
            | Failed (msg, q) -> Failed (msg, q))

let idtac : tac<unit> = ret ()

(* Set the current proofstate *)
let set (ps:proofstate) : tac<unit> =
    mk_tac (fun _ -> Success ((), ps))

(* Get the current proof state *)
let get : tac<proofstate> =
    mk_tac (fun ps -> Success (ps, ps))

let traise e =
    mk_tac (fun ps -> Failed (e, ps))

let log ps (f : unit -> unit) : unit =
    if ps.tac_verb_dbg
    then f ()
    else ()

let fail (msg:string) =
    mk_tac (fun ps ->
        if Env.debug ps.main_context (Options.Other "TacFail") then
          do_dump_proofstate ps ("TACTIC FAILING: " ^ msg);
        Failed (TacticFailure msg, ps)
    )

let catch (t : tac<'a>) : tac<BU.either<exn,'a>> =
    mk_tac (fun ps ->
            let tx = UF.new_transaction () in
            match run t ps with
            | Success (a, q) ->
                UF.commit tx;
                Success (BU.Inr a, q)
            | Failed (m, q) ->
                UF.rollback tx;
                let ps = { ps with freshness = q.freshness } in //propagate the freshness even on failures
                Success (BU.Inl m, ps)
           )

let recover (t : tac<'a>) : tac<BU.either<exn,'a>> =
    mk_tac (fun ps ->
            match run t ps with
            | Success (a, q) -> Success (BU.Inr a, q)
            | Failed (m, q)  -> Success (BU.Inl m, q)
           )

let trytac (t : tac<'a>) : tac<option<'a>> =
    bind (catch t) (fun r ->
    match r with
    | BU.Inr v -> ret (Some v)
    | BU.Inl _ -> ret None)

let trytac_exn (t : tac<'a>) : tac<option<'a>> =
    mk_tac (fun ps ->
    try run (trytac t) ps
    with | Errors.Err (_, msg)
         | Errors.Error (_, msg, _) ->
           log ps (fun () -> BU.print1 "trytac_exn error: (%s)" msg);
           Success (None, ps))

let rec mapM (f : 'a -> tac<'b>) (l : list<'a>) : tac<list<'b>> =
    match l with
    | [] -> ret []
    | x::xs ->
        bind (f x) (fun y ->
        bind (mapM f xs) (fun ys ->
        ret (y::ys)))

(* private *)
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

let check_valid_goals (gs:list<goal>) : unit =
  if Options.defensive () then
    List.iter check_valid_goal gs

let set_goals (gs:list<goal>) : tac<unit> =
  bind get (fun ps ->
  set ({ ps with goals = gs }))

let set_smt_goals (gs:list<goal>) : tac<unit> =
  bind get (fun ps ->
  set ({ ps with smt_goals = gs }))

let cur_goals : tac<list<goal>> =
  bind get (fun ps ->
  ret ps.goals)

let cur_goal : tac<goal> =
  bind cur_goals (function
  | [] -> fail "No more goals"
  | hd::tl ->
    match check_goal_solved' hd with
    | None -> ret hd
    | Some t ->
      BU.print2 "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
              (goal_to_string_verbose hd)
              (Print.term_to_string t);
      ret hd)

let remove_solved_goals : tac<unit> =
  bind cur_goals (fun gs ->
  let gs = List.filter (fun g -> not (check_goal_solved g)) gs in
  set_goals gs)

let dismiss_all : tac<unit> = set_goals []

let dismiss : tac<unit> =
    bind get (fun ps ->
    set ({ps with goals=List.tl ps.goals}))

let replace_cur (g:goal) : tac<unit> =
    bind get (fun ps ->
    check_valid_goal g;
    set ({ps with goals=g::(List.tl ps.goals)}))

let getopts : tac<FStar.Options.optionstate> =
    bind (trytac cur_goal) (function
    | Some g -> ret g.opts
    | None -> ret (FStar.Options.peek ()))

(* Some helpers to add goals, while also perhaps checking
 * that they are well formed (see check_valid_goal and
 * the --defensive debugging option. *)
let add_goals (gs:list<goal>) : tac<unit> =
    bind get (fun ps ->
    check_valid_goals gs;
    set ({ps with goals=gs@ps.goals}))

let add_smt_goals (gs:list<goal>) : tac<unit> =
    bind get (fun ps ->
    check_valid_goals gs;
    set ({ps with smt_goals=gs@ps.smt_goals}))

let push_goals (gs:list<goal>) : tac<unit> =
    bind get (fun ps ->
    check_valid_goals gs;
    set ({ps with goals=ps.goals@gs}))

let push_smt_goals (gs:list<goal>) : tac<unit> =
    bind get (fun ps ->
    check_valid_goals gs;
    set ({ps with smt_goals=ps.smt_goals@gs}))
(* /helpers *)

let add_implicits (i:implicits) : tac<unit> =
    bind get (fun ps ->
    set ({ps with all_implicits=i@ps.all_implicits}))

let new_uvar (reason:string) (env:env) (typ:typ) : tac<(term * ctx_uvar)> =
    // TODO: typ.pos should really never be a FStar.Range.range ... can it?
    let u, ctx_uvar, g_u =
        Env.new_implicit_var_aux reason typ.pos env typ Allow_untyped None
    in
    bind (add_implicits g_u.implicits) (fun _ ->
    ret (u, fst (List.hd ctx_uvar)))

let mk_irrelevant_goal (reason:string) (env:env) (phi:typ) opts label : tac<goal> =
    let typ = U.mk_squash (env.universe_of env phi) phi in
    bind (new_uvar reason env typ) (fun (_, ctx_uvar) ->
    let goal = mk_goal env ctx_uvar opts false label in
    ret goal)

let add_irrelevant_goal' (reason:string) (env:Env.env)
                         (phi:term) (opts:FStar.Options.optionstate)
                         (label:string) : tac<unit> =
    bind (mk_irrelevant_goal reason env phi opts label) (fun goal ->
    add_goals [goal])

let add_irrelevant_goal (base_goal:goal) (reason:string) 
                         (env:Env.env) (phi:term) : tac<unit> =
    add_irrelevant_goal' reason env phi base_goal.opts base_goal.label

let goal_of_guard (reason:string) (e:Env.env) (f:term) : tac<goal> =
  bind getopts (fun opts ->
  bind (mk_irrelevant_goal reason e f opts "") (fun goal ->
  let goal = { goal with is_guard = true } in
  ret goal))

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

let mlog f (cont : unit -> tac<'a>) : tac<'a> =
    bind get (fun ps -> log ps f; cont ())

let compress_implicits : tac<unit> =
    bind get (fun ps ->
    let imps = ps.all_implicits in
    let g = { Env.trivial_guard with implicits = imps } in
    let g = Rel.resolve_implicits_tac ps.main_context g in
    let ps' = { ps with all_implicits = g.implicits } in
    set ps')

#light "off"
module FStar.Tactics.Types

open FStar.All
open FStar.Syntax.Syntax
open FStar.TypeChecker.Env
module Options = FStar.Options
module SS = FStar.Syntax.Subst

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
    is_guard : bool; // Marks whether this goal arised from a guard during tactic runtime
                     // We make the distinction to be more user-friendly at times
}

let subst_goal subst goal = {
    goal with context = FStar.TypeChecker.Env.rename_env subst goal.context;
              witness = SS.subst subst goal.witness;
              goal_ty = SS.subst subst goal.goal_ty
}

type proofstate = {
    main_context : env;          //the shared top-level context for all goals
    main_goal    : goal;         //this is read only; it helps keep track of the goal we started working on initially
    all_implicits: implicits ;   //all the implicits currently open, partially resolved (unclear why we really need this)
    goals        : list<goal>;   //all the goals remaining to be solved
    smt_goals    : list<goal>;   //goals that have been deferred to SMT
    depth        : int;          //depth for tracing and debugging
    __dump       : proofstate -> string -> unit; // callback to dump_proofstate, to avoid an annoying ciruluarity
}

let subst_proof_state subst ps = {
    ps with main_goal = subst_goal subst ps.main_goal;
            goals = List.map (subst_goal subst) ps.goals
}


let decr_depth (ps:proofstate) : proofstate =
    { ps with depth = ps.depth - 1 }

let incr_depth (ps:proofstate) : proofstate =
    { ps with depth = ps.depth + 1 }

let tracepoint ps : unit =
    if Options.tactic_trace () || (ps.depth <= Options.tactic_trace_d ())
    then ps.__dump ps "TRACE"
    else ()

type direction =
    | TopDown
    | BottomUp

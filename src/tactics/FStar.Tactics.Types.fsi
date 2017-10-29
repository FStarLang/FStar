#light "off"
module FStar.Tactics.Types

open FStar.All
open FStar.Syntax.Syntax
open FStar.TypeChecker.Env
module N = FStar.TypeChecker.Normalize
module Range = FStar.Range

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

type proofstate = {
    main_context : env;          //the shared top-level context for all goals
    main_goal    : goal;         //this is read only; it helps keep track of the goal we started working on initially
    all_implicits: implicits ;   //all the implicits currently open, partially resolved (unclear why we really need this)
    goals        : list<goal>;   //all the goals remaining to be solved
    smt_goals    : list<goal>;   //goals that have been deferred to SMT
    depth        : int;          //depth for tracing and debugging
    __dump       : proofstate -> string -> unit; // callback to dump_proofstate, to avoid an annoying ciruluarity

    psc          : N.psc;        //primitive step context where we started execution
    entry_range  : Range.range;
}

val decr_depth : proofstate -> proofstate
val incr_depth : proofstate -> proofstate
val tracepoint : proofstate -> unit
val set_proofstate_range : proofstate -> Range.range -> proofstate

val subst_proof_state: subst_t -> proofstate -> proofstate

val set_ps_psc : N.psc -> proofstate -> proofstate

type direction =
    | TopDown
    | BottomUp

#light "off"
module FStar.Tactics.Monad

open FStar.Syntax.Syntax
open FStar.TypeChecker.Env
open FStar.Tactics.Result
open FStar.Tactics.Types
module BU  = FStar.Util
module O   = FStar.Options

(* Type of tactics *)
type tac<'a>

(* Simply unpack and run *)
val run : tac<'a> -> proofstate -> __result<'a>

(* Run, but catch exceptions as errors within the monad *)
val run_safe : tac<'a> -> proofstate -> __result<'a>

(* Monadic return *)
val ret : 'a -> tac<'a>

(* Monadic bind *)
val bind : tac<'a> -> ('a -> tac<'b>) -> tac<'b>

(* Get current proofstate *)
val get : tac<proofstate>

(* Get first goal *)
val cur_goal : tac<goal>

(* idtac: do nothing *)
val idtac : tac<unit>

(* Raise an exception *)
val traise : exn -> tac<'a>

(* A common failure. TODO: stop using string errors so much
 * and provide more structure. *)
val fail : string -> tac<'a>

(* Catch exceptions, restore UF graph on a failure *)
val catch : tac<'a> -> tac<BU.either<exn,'a>>

(* Catch exceptions, but keep UF graph at the time of the failure *)
val recover : tac<'a> -> tac<BU.either<exn,'a>>

(* Try running a tactic. If it fails, return None. *)
val trytac : tac<'a> -> tac<option<'a>>

(* As [trytac], but also catches exceptions and turns them into [None]. *)
val trytac_exn : tac<'a> -> tac<option<'a>>

(* Good old mapM *)
val mapM : ('a -> tac<'b>) -> list<'a> -> tac<list<'b>>

(* Set the current set of goals / SMT goals *)
val set_goals      : list<goal> -> tac<unit>
val set_smt_goals  : list<goal> -> tac<unit>

(* Add goals to the beginning of the list *)
val add_goals      : list<goal> -> tac<unit>
val add_smt_goals  : list<goal> -> tac<unit>

(* Add goals to the end of the list *)
val push_goals     : list<goal> -> tac<unit>
val push_smt_goals : list<goal> -> tac<unit>

(* Drop the first goal *)
val dismiss : tac<unit>

(* Drop all (non-SMT) goals *)
val dismiss_all : tac<unit>

(* Replace the current goal with another *)
val replace_cur : goal -> tac<unit>

(* Get the option state for the current goal, or the global one
if there are no goals. *)
val getopts : tac<FStar.Options.optionstate>

(* Add an implicit to the proofstate. The [all_implicits] field
 * is the only place where we keep track of open goals that need
 * to be solved. The [goals] and [smt_goals] fields are user-facing,
 * and do not really matter for correctness. *)
val add_implicits : implicits -> tac<unit>

(* Create a new uvar, and keep track of it in the proofstate to
 * ensure we solve it. *)
val new_uvar : string -> env -> typ -> tac<(term * ctx_uvar)>

(* Create a squashed goal from a given formula *)
val mk_irrelevant_goal : string -> env -> typ -> O.optionstate -> string -> tac<goal>

(* Create an add an irrelevant goal, allows to set options and label *)
val add_irrelevant_goal' : string -> env -> typ -> O.optionstate -> string -> tac<unit>

(* Create an add an irrelevant goal, taking a [base_goal] as a template for
 * options and label (which seldom need to be changed) *)
val add_irrelevant_goal : goal -> string -> env -> typ -> tac<unit>

(* Create a goal from a typechecking guard. *)
val goal_of_guard : string -> env -> term -> tac<goal>

(* Run a tactic [t], and it fails with a [TacticFailure] exception,
 * add a note in the error message. *)
val wrap_err : string -> tac<'a> -> tac<'a>

(* Call a (logging) function is verbose debugging is on *)
val log : proofstate -> (unit -> unit) -> unit

(* As above, but as a tac<> with an implicit bind for brevity *)
val mlog : (unit -> unit) -> (unit -> tac<'a>) -> tac<'a>

(* Discard the implicits in the proofstate that are already
 * solved, only matters for performance. *)
val compress_implicits : tac<unit>

(* Only leave goals that are unsolved in the main list *)
val remove_solved_goals : tac<unit>

(* DANGER AHEAD, DO NOT USE *)

(* Set the proofstate *)
val set : proofstate -> tac<unit>

(* Create a tactic *)
val mk_tac : (proofstate -> __result<'a>) -> tac<'a>

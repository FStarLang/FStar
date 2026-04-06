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
module FStarC.Tactics.Monad

open FStarC
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Env
open FStarC.Tactics.Result
open FStarC.Tactics.Types
open FStarC.Class.Monad
open FStarC.Errors.Msg
open FStarC.Effect

module Range = FStarC.Range
module O     = FStarC.Options

(* Type of tactics *)
type tac (a:Type0) : Type0 =
  ref proofstate -> ML a

instance val monad_tac : monad tac

(* DANGER AHEAD, DO NOT USE *)

(* Create a tactic *)
val mk_tac : (proofstate -> ML (__result 'a)) -> tac 'a

(* Simply unpack and run *)
val run : tac 'a -> proofstate -> ML (__result 'a)

(* Run, but catch exceptions as errors within the monad *)
val run_safe : tac 'a -> proofstate -> ML (__result 'a)

(* Set the proofstate *)
val set : proofstate -> tac unit

(* Get current proofstate *)
val get : tac proofstate

(* Raise an exception *)
val traise : exn -> tac 'a

(* Call a (logging) function if verbose debugging is on *)
val log : (unit -> ML unit) -> tac unit

(* A common failure. *)
val fail_doc : error_message -> tac 'a

(* A common failure. *)
val fail : string -> tac 'a

(* Catch exceptions, restore UF graph on a failure *)
val catch : tac 'a -> tac (either exn 'a)

(* Try running a tactic. If it fails, return None. *)
val trytac : tac 'a -> tac (option 'a)

(* As [trytac], but also catches exceptions and turns them into [None]. *)
val trytac_exn : tac 'a -> tac (option 'a)

(* iter combinator *)
val iter_tac (f: 'a -> ML (tac unit)) (l:list 'a) : tac unit

val fold_right (f: 'a -> 'b -> ML (tac 'b)) (l:list 'a) (x:'b) : tac 'b

(* Defensive checks. Will only do anything if --defensive is on. If so,
and some goal is ill-scoped, they will log a warning. *)
val check_valid_goal (g:goal) : ML unit
val check_valid_goals (gs:list goal) : ML unit

(* Set the current set of goals / SMT goals *)
val set_goals      : list goal -> tac unit
val set_smt_goals  : list goal -> tac unit

(* Get first goal *)
val cur_goal : tac goal

(* Only leave goals that are unsolved in the main list *)
val remove_solved_goals : tac unit

(* Drop all (non-SMT) goals *)
val dismiss_all : tac unit

(* Drop the first goal *)
val dismiss : tac unit

(* Replace the current goal with another *)
val replace_cur : goal -> tac unit

(* Get the option state for the current goal, or the global one
if there are no goals. *)
val getopts : tac FStarC.Options.optionstate

(* Add goals to the beginning of the list *)
val add_goals      : list goal -> tac unit
val add_smt_goals  : list goal -> tac unit

(* Add goals to the end of the list *)
val push_goals     : list goal -> tac unit
val push_smt_goals : list goal -> tac unit

(* Add an implicit to the proofstate. The [all_implicits] field
 * is the only place where we keep track of open goals that need
 * to be solved. The [goals] and [smt_goals] fields are user-facing,
 * and do not really matter for correctness. *)
val add_implicits : implicits -> tac unit

(* Create a new uvar, and keep track of it in the proofstate to
 * ensure we solve it. *)
val new_uvar : string -> env -> typ -> option should_check_uvar -> list ctx_uvar -> Range.t -> tac (term & ctx_uvar)

(* Create a squashed goal from a given formula *)
val mk_irrelevant_goal : string -> env -> typ -> option should_check_uvar -> Range.t -> O.optionstate -> string -> tac goal

(* Create an add an irrelevant goal, allows to set options and label *)
val add_irrelevant_goal' : string -> env -> typ -> option should_check_uvar -> Range.t -> O.optionstate -> string -> tac unit

(* Create an add an irrelevant goal, taking a [base_goal] as a template for
 * options and label (which seldom need to be changed) *)
val add_irrelevant_goal : goal -> string -> env -> typ -> option should_check_uvar -> tac unit

(* Create a goal from a typechecking guard. *)
val goal_of_guard : string -> env -> term -> option should_check_uvar -> Range.t -> tac goal

(* Run a tactic [t], and if it fails with a [TacticFailure] exception,
 * add a prefix to the error message. *)
val wrap_err_doc : pref:error_message -> tac 'a -> tac 'a

(* Run a tactic [t], and if it fails with a [TacticFailure] exception,
 * add a small string prefix to the first component of the error. *)
val wrap_err : pref:string -> tac 'a -> tac 'a

(* As above, but as a tac<> with an implicit bind for brevity (in code that does use
monadic notation...) *)
val mlog : (unit -> ML unit) -> (unit -> ML (tac 'a)) -> tac 'a

val if_verbose_tac: (unit -> ML (tac unit)) -> tac unit
val if_verbose: (unit -> ML unit) -> tac unit

(* Discard the implicits in the proofstate that are already
 * solved, only matters for performance. *)
val compress_implicits : tac unit

val is_goal_safe_as_well_typed (g:goal) : ML bool

(* inform the core of a well-typed goal *)
val register_goal (g:goal) : ML unit

(* Internal utilities *)
val get_phi : goal -> ML (option term)
val is_irrelevant : goal -> ML bool
val goal_typedness_deps : goal -> ML (list ctx_uvar)
val set_uvar_expected_typ (u:ctx_uvar) (t:typ) : ML unit
val mark_uvar_with_should_check_tag (u:ctx_uvar) (sc:should_check_uvar) : ML unit
val mark_uvar_as_already_checked (u:ctx_uvar) : ML unit
val mark_goal_implicit_already_checked (g:goal) : ML unit
val goal_with_type : goal -> typ -> ML goal

val divide (n:int) (l : tac 'a) (r : tac 'b) : tac ('a & 'b)
val focus (f:tac 'a) : tac 'a

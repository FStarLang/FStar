module FStarC.Hints

open FStarC
open FStarC
open FStarC.Effect

(** Hints. *)
type hint = {
    hint_name:string; //name associated to the top-level term in the source program
    hint_index:int; //the nth query associated with that top-level term
    fuel:int; //fuel for unrolling recursive functions
    ifuel:int; //fuel for inverting inductive datatypes
    unsat_core:option (list string); //unsat core, if requested
    query_elapsed_time:int; //time in milliseconds taken for the query, to decide if a fresh replay is worth it
    hash:option string; //hash of the smt2 query that last succeeded
}

type hints = list (option hint)

type hints_db = {
    module_digest:string;
    hints: hints
}

type hints_read_result =
  | HintsOK of hints_db
  | MalformedJson
  | UnableToOpen

val write_hints: string -> hints_db -> unit
val read_hints: string -> hints_read_result

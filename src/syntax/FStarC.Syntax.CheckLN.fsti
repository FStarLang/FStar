module FStarC.Syntax.CheckLN

open FStarC.Syntax.Syntax

(* Checks if, at most, n indices escape from a term.
For both term and universe variables. *)
val is_ln' (n:int) (t:term) : bool

(* Checks if a term is locally nameless. Equal to [is_ln' 0] *)
val is_ln (t:term) : bool

module MatchGuard
open FStar.All
open FStar.IO

(* [when] clauses are only supported in lax mode. *)
#set-options "--lax"

(* Regression test for an off-by-|s| scoping bug in the normalizer's iota
   rule.  When a branch has a [when] clause, the reduction used to be turned
   into [if w then <this branch> else match scrutinee with <remaining
   branches>], and the whole thing was normalized in an environment already
   extended with this branch's pattern variables.  The remaining branches are
   closed with respect to the environment *before* that extension, so every de
   Bruijn index in them was read one (or more) slots too shallow.

   The shape below is the minimal trigger: a definite match on a concrete
   scrutinee, a first branch whose pattern binds something and whose guard
   cannot be decided, and a later branch that both binds something and refers
   to an enclosing binder. *)
let pick (n:int) : int =
  match (3, 4) with
  | p when n > 0 -> fst p + n
  | (a, b) -> a + b + n

(* Same, one level deeper: the mis-scoped branch is itself guarded. *)
let pick2 (n:int) (m:int) : int =
  match (3, 4) with
  | p when n > 0 -> fst p + n
  | q when m > 0 -> snd q + m
  | (a, b) -> a + b + n + m

let main () : ML unit =
  print_string (string_of_int (pick 5));
  print_string " ";
  print_string (string_of_int (pick (-1)));
  print_string " ";
  print_string (string_of_int (pick2 5 0));
  print_string " ";
  print_string (string_of_int (pick2 0 5));
  print_string " ";
  print_string (string_of_int (pick2 (-1) (-1)));
  print_string "\n"

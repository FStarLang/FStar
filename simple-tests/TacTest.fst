module TacTest

open FStar.Tactics.Effect

/// Tactic "primitives" (in the real library these are compiler builtins
/// registered as primitive steps).
assume val dump    : string -> Tac unit
assume val trivial : unit -> Tac unit
assume val fail    : #a:Type -> string -> Tac a
assume val cur_goal_str : unit -> Tac string
assume val ngoals  : unit -> Tac int

/// Tactic combinators written in F* itself.
let rec repeat_n (n:int) (t: unit -> Tac unit) : Tac unit =
  if n <= 0 then () else (t (); repeat_n (n - 1) t)

let dump_goal () : Tac unit =
  let s = cur_goal_str () in
  dump s

let finish () : Tac unit =
  let n = ngoals () in
  if n = 0 then () else (dump_goal (); fail "goals remain")

/// Tac can call Pure/Div/ML code (lattice: PURE ~> DIV ~> ALL ~> TAC).
let pure_helper (x:int) : Pure int (requires (x >= 0)) (ensures (fun r -> r == x + 1)) = x + 1

let uses_pure () : Tac int =
  let n = ngoals () in
  if n >= 0 then pure_helper n else fail "negative"

/// Specs on tactics still work: an effect abbreviation's own parameters are
/// positional, and any use-site requires/ensures is conjoined with them.
let checked (x:int) : Tac int (requires (x >= 0)) (ensures (fun r -> r >= x)) =
  dump "checked";
  x + 1

/// Effect definitions only matter for extraction, but they do let us build a
/// tactic from its representation with `TAC?.reflect`.
assume val get_ps : ref_proofstate -> FStar.All.ML int

let goal_count () : Tac int =
  TAC?.reflect (fun ps -> get_ps ps)

/// A local `let rec` inside a tactic: reification must commute with it,
/// otherwise extraction fails with "should have been handled at Tm_abs level".
let local_rec (l:list int) : Tac int =
  let rec sum (l:list int) : Tac int =
    match l with
    | [] -> 0
    | hd :: tl -> hd + sum tl
  in
  let n = ngoals () in
  sum l + n

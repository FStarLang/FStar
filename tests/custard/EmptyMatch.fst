module EmptyMatch

(* A match with no branches -- on a value of an empty type -- has no spelling
   in OCaml or F#: both printed it as [(match e with)], a syntax error.  The
   [prune] pass now turns it into an [EUnreachable], keeping the scrutinee
   only when evaluating it is observable.

   [absurd] is the pure case (the scrutinee is a variable and goes away);
   [f] is the impure one (the scrutinee is a [false_elim], which must still be
   evaluated first).  Both are reachable but never taken. *)

let absurd (#a:Type) (x:empty) : a = match x with

let f (x:nat) : int =
  if x < 0 then (match (false_elim () <: empty) with) else x + 1

let g (b:bool{b}) (x:nat) : int =
  if b then x else (let e : empty = false_elim () in absurd e)

let main () : FStar.All.ML unit =
  FStar.IO.print_string (string_of_int (f 3 + g true 4) ^ "\n")

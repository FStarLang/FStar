module RetArity

(* The arrows an eta-short definition's extra binders consume can be hidden
   behind a chain of abbreviations: [outer] is one arrow and a *second*
   abbreviation, which is two more.  All three have to be peeled off the
   result type, or the definition claims an arity it does not have.

   The body uses its last binder so that it is not a *forwarder* in the sense
   of section 27.4; otherwise the whole call collapses to [g] and there is no
   definition left to check. *)
type inner (n:nat) = int -> bool -> nat
type outer (n:nat) = string -> inner n

let f (g:nat) : outer g = fun frame post t -> if t then g else 0

let main () : FStar.All.ML unit =
  FStar.IO.print_string (string_of_int (f 3 "a" 1 true) ^ "\n")

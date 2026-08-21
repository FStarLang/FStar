module RetArity

(* The arrows an eta-short definition's extra binders consume can be hidden
   behind a chain of abbreviations: [outer] is one arrow and a *second*
   abbreviation, which is two more.  All three have to be peeled off the
   result type, or the definition claims an arity it does not have. *)
type inner (n:nat) = int -> bool -> nat
type outer (n:nat) = string -> inner n

let f (g:nat) : outer g = fun frame post t -> g

let main () : FStar.All.ML unit =
  FStar.IO.print_string (string_of_int (f 3 "a" 1 true) ^ "\n")

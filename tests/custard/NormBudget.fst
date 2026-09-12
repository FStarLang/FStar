module NormBudget
open FStar.All

(* Section 3.6: normalization is bounded, so a term that diverges under
   reduction is a diagnosable error rather than a hang.  Termination is an SMT
   query, so admitting queries is what lets a divergent definition be [Tot] --
   and [Tot] is the point: a [Dv] argument is a runtime value that no key ever
   normalizes, so it would not exercise this at all. *)
#push-options "--admit_smt_queries true"
(* Total as far as the typechecker is concerned, and divergent as far as the
   normalizer is concerned, which is exactly the combination the budget is
   there to survive. *)
let rec spin (n:int) : Tot int = spin (n + 1)
#pop-options

let g ([@@@monomorphize] n:int) : ML int = n

let main () : ML unit =
  FStar.IO.print_string (string_of_int (g (spin 0)))

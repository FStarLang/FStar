module AbsDropFree
open FStar.All

(* Section 5.2's rule in [extract_letbinding] and in [expr_of_term]'s
   [Tm_abs].  A binder dropped there is one the body may still name: the
   occurrence sits where the erasure left [unit], so [()] is the closure the
   body is owed.  Without it the OCaml backend reported [Unbound value "pf"].

   [mk] is the top-level case -- the [squash] binder is written into the
   second component of a dependent pair whose field is erased -- and [local]
   is the lambda one, where the same binder belongs to an inner [fun]. *)

let mk (n:nat) (pf : squash (n >= 0)) : (x:nat & squash (x >= 0)) =
  (| n, pf |)

let local (n:nat) : nat =
  let h : squash (n >= 0) -> nat -> (x:nat & squash (x >= 0)) =
    fun pf m -> (| m + n, pf |) in
  dfst (h () 1)

let main () : ML unit =
  FStar.IO.print_string (string_of_int (dfst (mk 3 ())) ^ "\n");
  FStar.IO.print_string (string_of_int (local 4) ^ "\n")

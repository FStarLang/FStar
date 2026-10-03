module LocalErase
open FStar.All
open FStar.IO

(* Section 115.  A local [let rec] is lifted to a top-level definition, and the
   lifting kept every value binder -- including one whose type is erased.  The
   caller, which erases, then passed one argument fewer than the lifted
   function declares, and the result was an arity mismatch that the backends
   report in their own terms.  Erased binders are dropped at the lift too. *)
let count (n:nat) : nat =
  let rec go (p:FStar.Ghost.erased bool) (n:nat) : Tot nat (decreases n) =
    if n = 0 then 0 else 1 + go p (n - 1)
  in go (FStar.Ghost.hide true) n

let main () : ML unit =
  print_string (string_of_int (count 3)); print_string "\n"

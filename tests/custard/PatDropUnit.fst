module PatDropUnit
open FStar.All

(* Section 5.2's rule in [pat_of_pat].  A constructor field with no runtime
   representation has its sub-pattern deleted here rather than erased by
   [Layout], and the body may still name it -- so the name has to be rebound
   to [()] around the body, or it reaches the backend free and OCaml reports
   an unbound value.

   The body therefore has to *use* the binder: a dropped sub-pattern whose
   name goes unmentioned was never a problem.  Writing it into the erased
   component of a dependent pair is the smallest way to do that, and is what
   EverParse hit.

   Both spellings of the field are covered, because what decides it is the
   constructor's own flags rather than how the type was written: [myunit] is
   an abbreviation of [unit], [squash True] is a proposition. *)

type myunit = unit

noeq type t = | C : myunit -> nat -> t
noeq type u = | D : squash True -> nat -> u

let f (x:t) : (n:nat & myunit) = match x with | C pf n -> (| n, pf |)
let g (x:u) : (n:nat & squash True) = match x with | D pf n -> (| n, pf |)

(* The guard is closed by the same rebinding as the body. *)
let h (x:t) : (n:nat & myunit) =
  match x with
  | C pf n -> if (let _ = pf in n > 0) then (| n, pf |) else (| 0, pf |)

let main () : ML unit =
  FStar.IO.print_string (string_of_int (dfst (f (C () 3))) ^ "\n");
  FStar.IO.print_string (string_of_int (dfst (g (D () 4))) ^ "\n");
  FStar.IO.print_string (string_of_int (dfst (h (C () 5))) ^ "\n")

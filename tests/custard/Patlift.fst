module Patlift

open FStar.All

(* A lambda-lifted local [let rec] whose binders are *patterns*: F* turns each
   into a fresh [uu___] and matches on the tuple of them all.  Two such
   binders must not collapse into one. *)
(* The termination check cannot see through the tuple patterns, and a
   [decreases] is not allowed on a [let] with inlined patterns. *)
#push-options "--admit_smt_queries true"
let go (p : list int & int) =
  let rec loop (acc, k) (xs, y) =
    match xs with
    | [] -> acc + k + y
    | x :: tl -> loop ((acc + x), k) (tl, y)
  in
  loop (0, 5) p
#pop-options

let main () : ML unit =
  FStar.IO.print_string (string_of_int (go ([1;2;3], 4)));
  FStar.IO.print_string "\n"

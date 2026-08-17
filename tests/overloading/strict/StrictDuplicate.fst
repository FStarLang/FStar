module StrictDuplicate
#set-options "--warn_error +362"
open StrictInt
open StrictBool

(* The typechecker elaborates a declaration more than once: the two phases
   of tc_decl, and, for a `let rec`, the computation type is checked while
   extracting the annotation as well as with the body. So this occurrence
   of `same` reaches overload resolution several times, and reporting it
   once per visit would bury the reader in copies of one fact.

   362 is demoted to a warning here so that the run continues and prints
   every report it is going to print; the point of the test is the count. *)
let rec g (n:int) : Pure int (requires (same >= 0)) (ensures (fun _ -> True)) =
  if n <= 0 then 0 else g (n - 1)

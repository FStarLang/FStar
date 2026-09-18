module SplitAny
open FStar.All

(* Section 115.  A field whose type is [TAny] is matched by splitting the
   branch: the outer pattern drops the field and an inner match on it takes
   over.  That moves a test *inside* a branch that has already been chosen,
   and a test inside a branch has nowhere to fail to -- so when the inner
   pattern was refutable, a value that did not match it fell out of the match
   entirely instead of reaching the branches below.

   [P true true] matches no branch of the inner match and has to reach the
   catch-all: it must print 2, not 1.  The lemma states that in F*, so the
   generated code and the source have to agree. *)
noeq type pair = | P : b:bool -> data:(if b then bool else unit) -> pair

let pick (p:pair) : int =
  match p with
  | P true false -> 1
  | _ -> 2

let expected_fallthrough () : Lemma (pick (P true true) == 2) = ()

let main () : ML unit =
  FStar.IO.print_string (string_of_int (pick (P true false)) ^ "\n");
  FStar.IO.print_string (string_of_int (pick (P true true)) ^ "\n");
  FStar.IO.print_string (string_of_int (pick (P false ())) ^ "\n")

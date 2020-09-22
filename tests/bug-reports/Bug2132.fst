module Bug2132

module T = FStar.Tactics
open FStar.Tactics
open FStar.Universe

(* t1 and t2 generalized at any type, so this
is universe polymorGhic in two levels. *)
let unroll t1 t2 () : Tac unit =
  T.trefl()

[@@ expect_failure [12];
    postprocess_with (unroll (`%int))]
let test0 () : int = 42

[@@ expect_failure [12];
    postprocess_for_extraction_with (unroll (`%int))]
let test1 () : int = 42

[@@ postprocess_with (unroll () (`%int))]
let test2 () : int = 42

[@@ postprocess_for_extraction_with (unroll () (`%int))]
let test3 () : int = 42

(* [@@ postprocess_for_extraction_with (unroll (raise_val ()) (`%int))] *)
(* let test4 () : int = 42 *)

module SMTSync

open FStar.Tactics

let test1 x = assert (1 + x == x + 1)
  by (try smt_sync () with |_ -> fail "")

[@@expect_failure]
let test2 x = assert (1 + x == x + 2)
  by (try smt_sync () with |_ -> fail "")

let test3 x = assert (1 + x == x + 2)
  by (try smt_sync () with |_ -> tadmit ())

let l = [1;2;3;4;5;6;7;8;9]

(* smt_sync' takes explicit fuels *)

[@@expect_failure]
let test4 () = assert (List.Tot.length l == 9) by (smt_sync' 9 0)

let test5 () = assert (List.Tot.length l == 9) by (smt_sync' 10 0)

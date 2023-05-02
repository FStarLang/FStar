module Bug2899

open FStar.Tactics
#set-options "--warn_error -266" // failed unembeddings

[@@expect_failure [228]]
let test0 = assert(True) by admit()

[@@expect_failure [228]]
let test1 = assert(True) by (match admit () with | 0 -> dump "x" | _ -> dump "y")

[@@expect_failure [228]]
let test2 = assert(True) by (dump (admit ()))

(* From #1316 *)
[@@expect_failure [228]]
let eval_tactic (tac : unit -> Tac unit) : unit = assert_by_tactic True tac

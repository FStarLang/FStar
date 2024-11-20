module Bug2981

open FStar.Tactics.V2

assume val token (g:env) : Type0
assume val check (g:env) : Tac (option (token g))

[@@expect_failure [56]]
let test1 () : Tac unit =
  let r = check (cur_env()) in
  ()

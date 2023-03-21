module Bug2849b

let pure () : int =
  let rec f () : int = 1
  and g () = 2
  and h () = 3
  in f ()

let _ = assert_norm (pure () == 1)

module T = FStar.Tactics

let t1 () : T.Tac unit =
  let rec f (): T.Tac unit = T.fail "fail_f"
  and g () : T.Tac unit = ()
  and h () : T.Tac unit = T.fail "fail_g"
  in g ()

let tac1 (): unit = assert (True) by (t1 ())

let t2 () : T.Tac unit =
  let rec f (): T.Tac unit = T.fail "fail_f"
  and g () : T.Tac unit = ()
  and h () : T.Tac unit = T.fail "fail_g"
  in f ()

[@@expect_failure]
let tac2 (): unit = assert (True) by (t2 ())

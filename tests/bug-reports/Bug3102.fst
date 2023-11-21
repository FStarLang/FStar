module Bug3102

let eqto #a (t:a) : Type = x:a{x==t}
assume val tt : t:int -> Tot (eqto t)

[@@expect_failure [56]]
let min =
  fun (t1:int) ->
    let e1 = t1 in
    tt e1

open FStar.Tactics.V2

let test0 : g:env -> t1:term -> t2:term -> Tac (ret_t (subtyping_token g t1 t2)) =
  fun (g:env) (t1 t2:term) ->
    let e2 = t2 in
    check_subtyping g t1 e2

[@@expect_failure [54]]
// * Error 54 at Bug3102.fst(28,4-28,27):
//   - (*?u23*) _ g t1 t2 is not equal to the expected type e2
// Not great... but it does make sense as we wrote an _ that can only
// mention g t1 and t2, and the escapes check does not trigger in the same way
// as above
let test1 : g:env -> t1:term -> t2:term -> Tac (ret_t (subtyping_token g t1 _)) =
  fun (g:env) (t1 t2:term) ->
    let e2 = t2 in
    check_subtyping g t1 e2

[@@expect_failure [54]]
let test2 : g:env -> t1:term -> t2:term -> Tac _ =
  fun (g:env) (t1 t2:term) ->
    let e2 = t2 in
    check_subtyping g t1 e2

[@@expect_failure [56]]
let test3 =
  fun (g:env) (t1 t2:term) ->
    let e2 = t2 in
    check_subtyping g t1 e2

assume val ff : x:int -> y:int{y == x}

[@@expect_failure [56]]
let gg =
  fun (x:int) ->
    let z = x in
    ff z

assume val f : x:int -> Tac (y:int{y == x})

[@@expect_failure [56]]
let g =
  fun (x:int) ->
    let z = x in
    f z

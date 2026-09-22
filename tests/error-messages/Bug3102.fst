module Bug3102

(* A let-bound variable that escapes into the result type is now closed
   existentially rather than rejected, so the [56] cases are gone; what is left
   here is the message quality of the [66] and [54] cases. *)

let eqto #a (t:a) : Type = x:a{x==t}
assume val tt : t:int -> Tot (eqto t)

let min =
  fun (t1:int) ->
    let e1 = t1 in
    tt e1

open FStar.Tactics.V2
open FStar.Reflection.TermSpec

let test0 : g:env -> t1:term -> t2:term -> Tac (ret_t (subtyping_token g (denote_term t1) (denote_term t2))) =
  fun (g:env) (t1 t2:term) ->
    let e2 = t2 in
    check_subtyping g t1 e2

[@@expect_failure [66]]
let test1 : g:env -> t1:term -> t2:term -> Tac (ret_t (subtyping_token g (denote_term t1) _)) =
  fun (g:env) (t1 t2:term) ->
    let e2 = t2 in
    check_subtyping g t1 e2

[@@expect_failure [54]]
let test2 : g:env -> t1:term -> t2:term -> Tac _ =
  fun (g:env) (t1 t2:term) ->
    let e2 = t2 in
    check_subtyping g t1 e2

let test3 =
  fun (g:env) (t1 t2:term) ->
    let e2 = t2 in
    check_subtyping g t1 e2

assume val ff : x:int -> y:int{y == x}

let gg =
  fun (x:int) ->
    let z = x in
    ff z

assume val f : x:int -> Tac (y:int{y == x})

let g =
  fun (x:int) ->
    let z = x in
    f z

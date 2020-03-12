module Bug1940c

(* Minimization by Exe *)

let ee (b : bool) : Type =
    s: bool { s == b }

type t = | C

let f (a:t) =
  match a with
  | C -> false

let g (a:t) =
  match a with
  | C -> true

[@expect_failure]
let foo (a:t) (x: ee (f a)) : ee (g a) = x

let test (s:ee false) : Lemma False =
  assert (foo C s == true)

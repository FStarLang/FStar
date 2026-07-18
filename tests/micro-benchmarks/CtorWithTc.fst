module CtorWithTc

open FStar.Class.Eq.Raw

noeq
type pack =
  | Mk :
    #t:Type0 ->
    {| dict : deq t |} ->
    x : t ->
    pack

let p1 (x:pack) : Type0 =
  match x with
  | Mk #t #_ x -> t

let p2 (x:pack) : deq (p1 x) =
  match x with
  | Mk #_ #d _ -> d

let x = Mk 5

let y = Mk?.dict x

[@@expect_failure [175]] // branch is missing implicit
let p2' (x:pack) : deq (p1 x) =
  match x with
  | Mk #_ d _ -> d

let p3 (x:pack) : p1 x =
  match x with
  | Mk #_ #_ e -> e

let p3' (x:pack) : p1 x =
  match x with
  | Mk e -> e

let _ = assert_norm (p3' x == 5)

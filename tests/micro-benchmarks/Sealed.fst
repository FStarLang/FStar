module Sealed

open FStar.Mul
open FStar.Sealed
open FStar.Tactics

let test1 (x y : int) =
  sealed_singl (seal x) (seal y);
  assert (seal x == seal y)

[@@expect_failure [19]]
let test2 (x y : int) =
  assert (seal x == seal y ==> x == y)

[@@expect_failure [19]]
let test3 (x y : int) =
  assert_norm (seal x =!= seal y)

(* Sealed values do not have to be equal at
different types. *)
[@@expect_failure [19]]
let test4 (x : int) (y : nat) =
  assert (seal #int x == seal #nat y)

let rec sfac (n:nat) : Tac (sealed nat) =
  match n with
  | 0 -> seal 1
  | _ -> seal (n * unseal (sfac (n-1)))

(* Testing it actually runs *)
let _ = assert True by begin
  let r = unseal (sfac 5) in
  if r <> 120 then
    fail "bad"
end

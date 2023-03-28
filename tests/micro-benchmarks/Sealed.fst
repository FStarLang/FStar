module Sealed

open FStar.Mul
open FStar.Sealed
open FStar.Tactics

let test1 (x y : int) =
  sealed_singl (seal x) (seal y);
  assert (seal x == seal y)

// Using an SMT pattern
let is_sealed #a (s:sealed a) : prop = True

let my_seal (#a:Type) (x:a) : s:sealed a { is_sealed s } = seal x

let my_seal_singleton (#a:Type) (x y : sealed a)
  : Lemma 
    (x == y)
    [SMTPat (is_sealed x);
     SMTPat (is_sealed y)]
  = sealed_singl x y

let test1_auto (x y : int) =
  assert (my_seal x == my_seal y)

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

//With inhabited seals
module I = FStar.Sealed.Inhabited
let snat = I.sealed #nat 0
let sealnat x : snat = I.seal x
let sealnat_auto (x y : nat) =
  assert (sealnat x == sealnat y)
let rec snatfac (n:nat) : Tac snat =
  match n with
  | 0 -> sealnat 1
  | _ -> sealnat (n * unseal (snatfac (n-1)))

let _ = assert True by begin
  let r = unseal (snatfac 5) in
  if r <> 120 then
    fail "bad"
end

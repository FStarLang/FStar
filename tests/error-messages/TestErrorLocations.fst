(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module TestErrorLocations
#set-options "--fuel 0 --ifuel 0"
//reports failing call to assert, and the failing formula
[@@expect_failure [19]]
let test0 = assert (0==1)

//reports failing call to assert, and the 1st conjunct of the failing formula
[@@expect_failure [19]]
let test1 = assert (0==1 /\ 0==0)


assume val test2_aux: x:int -> Pure int (requires (x >= 0) /\ 0=0 )
				    (ensures (fun x -> True))
[@@expect_failure [19]]
let test2 (x:int) =
  let y = test2_aux x in //reports failing call, and the definition site of the relevant conjunct of requires clause
  y + 1

[@@expect_failure [19]]
let test3 x =
  let f = test2_aux in //local renaming
  let y = f (-1) in       //should still report this location
  y + 1

assume val test4_aux: nat -> Tot int
[@@expect_failure [19]]
let test4 (x:int) =
  let y = test4_aux x in //subtyping check failed, expected nat, got int
  y + 1

val test5: x:int -> Pure int (requires (b2t (x <> 0))) (ensures (fun x -> 0 >= 0 /\ x >= 0))
[@@expect_failure [19]]
let test5 x = x + 1 //reports failing 2nd conjunct of post-condition


//!!!!!!!!!!!!!!!!!!!!!!!!
// reports a terrible location in prims, because of an optimization
// that blows away most of the VC because of the False post-condition
//!!!!!!!!!!!!!!!!!!!!!!!!

val test6: unit -> Lemma (0==1)
[@@expect_failure [19]]
let test6 () = () //reporting a failing post-condition

val test7: unit -> Lemma False
[@@expect_failure [19]]
let test7 () = ()

assume val test8_aux: x:nat -> Tot nat
[@@expect_failure [19]]
let test8 (x:int{test8_aux x = 0}) = () //reports expected nat; got int

assume val test9_aux : x:int -> Pure bool (requires (b2t (x >= 0))) (ensures (fun x -> True))
[@@expect_failure [19]]
assume val test9 : x:int{test9_aux x} -> Tot unit //should report a failing assertion in the refinement (f x)

(* --detail_errors has regressed
#set-options "--detail_errors"
assume val p1 : bool
let p2 = true
assume val p3 : bool
assume val p4 : bool

let test10 = 
  assert p1;
  assert p2;
  assert p3;
  assert (p2 \/ p3)
*)


[@@expect_failure [19]]
let test_elim_exists () : unit
= eliminate exists (n: nat). (n = 0)
  returns True
  with pf_zero . assert(n = 0)

open FStar.Mul

[@@expect_failure [19]]
let test_elim_forall () : unit
= eliminate forall (n:nat). n = 0
  with 0

[@@expect_failure [19]]
let test_elim_and (p q:prop) : unit
= eliminate p /\ q
  returns q
  with pp qq. qq

[@@expect_failure [19]]
let test_elim_and (p q:prop) (_:squash p) : unit
= eliminate p /\ q
  returns q
  with pp qq. qq

[@@expect_failure [19]]
let test_elim_or (p q:prop) : unit
= eliminate p \/ q
  returns False
  with pp. admit()
  and qq. admit()
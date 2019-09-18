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

module Test

/// Testing the HoareST layered effect from HoareST.fst

open HoareST

/// Note that we don't need FStar.ST since the layered effects abstraction does not need it for verification

#set-options "--max_fuel 0 --initial_ifuel 4 --max_ifuel 4 --using_facts_from '* -FStar.ST'"


/// In this test:
///   `3` is first lifted from `Tot` to `HoareST`
///   and then its type is weakened to the annotated type

let test ()
: HoareST int
  (fun _ -> True)
  (fun h0 r h1 -> r > 1 /\ h0 == h1)
= 3

/// This fails since the postcondition is incorrect

[@expect_failure]
let test_fail ()
: HoareST int
  (fun _ -> True)
  (fun _ r _ -> r > 3)
= 3


/// Testing binds

let test2 ()
: HoareST int
  (fun _ -> True)
  (fun h0 r h1 -> r >= 4 /\ h0 == h1)
= let x = test () in
  let y = test () in
  x + y

let f_pure ()
: Pure int
  (requires True)
  (ensures fun x -> x > 2)
= 3

/// More tests for bind, including lifts from Pure

let test3 ()
: HoareST int
  (fun _ -> True)
  (fun _ r _ -> r >= 5)
= let x = test () in
  let y = f_pure () in
  x + y

/// This test relies on the return inserted for f_pure ()
/// The wp of f_pure is too weak to prove the postcondition otherwise

let test4 ()
: HoareST int
  (fun _ -> True)
  (fun _ r _ -> r == 3)
= let _ = test () in
  f_pure ()

/// This test fails if we use an alternative lift from PURE to HoareST that makes post parametric
///   (rather than using the (~ wp (fun ...)) encoding that we use currently)

let test5 ()
: HoareST int
  (fun _ -> True)
  (fun h0 r h1 -> True)
= let y = test () in
  y

/// It relies on inserting return for f_pure

let test6 ()
: HoareST int
  (fun _ -> True)
  (fun _ r _ -> r == 3)
= let x = f_pure () in
  let y = test () in
  x


/// Testing basic pattern matching

assume val test7 (x:int)
: HoareST int
  (fun _ -> x > 0)
  (fun _ y _ -> y > x)

let test8 (l:list int)
: HoareST int (fun _ -> Cons? l /\ Cons?.hd l > 0) (fun _ _ _ -> True)
= match l with
  | hd::_ -> test7 hd




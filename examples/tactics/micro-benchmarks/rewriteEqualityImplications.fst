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
(* Here's the incantation I use to check this file: *)
(* $ fstar rewriteEqualityImplications.fst --debug RewriteEqualityImplications --debug_level Low | grep "\(Got goal\)\|Checking top-level decl let" *)
(* Notice the "Got goal" output, in particular---that's the result of preprocessing the VC for each top-level term. *)
(* Each term results in 0 or more queries that get sent to Z3 *)
module RewriteEqualityImplications
//#reset-options "--log_queries"  //<-- Look at the queries-rewriteEqualityImplications.smt2 file, if this is turned on
let test_1 = assert (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y))                               //proven by tactic
let test_2 = assert (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z))    //proven by tactic
let test_3 () = assert (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z)) //proven by tactic

let good (x:int) = true
let test_4 () = assert (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z) /\ good x) //(good x) goes to SMT

unfold let good_2 (x:int) = True
let test_5 () = assert (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z) /\ good_2 x) //proven by tactic

unfold let good_3 (x:int) = true
let test_6 () = assert (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z) /\ good_3 x) //b2t true, goes to SMT (fix)

let test_7 =
  let x = 10 in
  assert (x + 0 == 10) //proven by tactic

assume type pred_1 : int -> Type0
assume Pred1_saturated: forall x. pred_1 x

assume type pred_2 : int -> Type0
assume Pred1_saturated: forall x. pred_1 x ==> pred_2 x

let test_8 =
  let x = 10 in
  assert (x + 0 == 10); //proven by tactic
  assert (pred_1 x);     //1 SMT sub-goal
  assert (pred_2 x)      //2 another SMT sub-goal

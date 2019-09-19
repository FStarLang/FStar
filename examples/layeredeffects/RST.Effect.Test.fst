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

module RST.Effect.Test

open Steel.Resource
open Steel.RST

open RST.Effect

/// Tests for RST as a layered effect

#set-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 2 --max_ifuel 2 --using_facts_from '* \
  -FStar.Seq \
  -FStar.ST \
  -FStar.HyperStack \
  -FStar.Monotonic.HyperStack
  -FStar.Heap
  -FStar.Monotonic.Heap \
  -FStar.Tactics \
  -FStar.Reflection \
  -LowStar \
  -FStar.ModifiesGen'"

assume val r1 : r:resource{r.t == nat}

assume val test5 (x:int)
: RST unit r1 (fun _ -> r1)
  (fun _ -> x > 0)
  (fun _ _ _ -> True)

#set-options "--debug RST.Effect.Test --debug_level Rel --debug_level Extreme --print_full_names --print_universes --ugly --debug_level TwoPhases --debug_level LayeredEffects --print_implicits --print_bound_var_types --debug_level SMTEncoding --debug_level SMTQuery" //--print_effect_args"

//[@expect_failure]

#restart-solver
#set-options "--log_queries"

let test6 (l:list int)
: RST unit r1 (fun _ -> r1)
  (fun _ -> Cons? l /\ Cons?.hd l > 0)
  (fun _ _ _ -> True)
= match l with
  | hd::_ -> test5 hd


// (*
//  * This code doesn't typecheck without the <: Tot nat ascription
//  * What happens is:
//  *   We first typecheck 2 : Tot int
//  *   Then the expected type in the environment is nat (coming from the return type annotation)
//  *   So we check that (2 : int <: nat)
//  *   This succeeds with guard (2 >= 0),
//  *   But in the process we end up inserting a return and make (2 : PURE nat (pure_return_wp int 2))
//  *   Note the type int in the pure_return_wp -- this is because we end up using the initial type
//  *   (TcTerm.value_check_expected_type - call to TcUtil.return_value)
//  *
//  *   Now the problem is, when we lift PURE nat (pure_return_wp int 2) to RST,
//  *     the unification happens at type nat,
//  *     and we unify (pure_return_wp int 2) to the (wp:pure_wp nat) argument of lift
//  *     and this fails to typecheck (generates an smt query that forall (x:int). x >= 0)
//  *
//  *   Adding the (Tot nat) ascription ensures that the return is inserted at type nat, and then we are good
//  *
//  *   We need to figure out a way to handle this, not typecheck these binders in layered effect combinators?
//  *)
// let test1 ()
// : RST nat emp (fun _ -> emp) (fun _ -> True) (fun _ r _ -> r == 2)
// = (2 <: Tot nat)


// assume val r2 : r:resource{r.t == nat}
// assume val r3 : r:resource{r.t == nat}


// assume val f1
// : x:nat ->
//   RST unit r1 (fun _ -> r2)
//   (fun (rm:rmem r1) -> rm r1 == 2)
//   (fun (rm_in:rmem r1) _ (rm_out:rmem r2) -> rm_out r2 == rm_in r1 + x)

// assume val f2
// : x:nat ->
//   RST unit r2 (fun _ -> r3)
//   (fun rm -> rm r2 == 2)
//   (fun rm_in _ rm_out -> rm_out r3 == rm_in r2 + x)

// assume val f3
// : x:nat ->
//   RST unit r3 (fun _ -> r3)
//   (fun rm -> rm r3 == 2)
//   (fun rm_in _ rm_out -> rm_out r3 == rm_in r3 + x)

// let test2 ()
// : RST unit r1 (fun _ -> r3)
//   (fun rm -> rm r1 == 2)
//   (fun rm_in x rm_out -> rm_out r3 > 2)
// = f1 0; f2 0; f3 3

// assume Can_be_split_into_emp:
//   forall (r:resource). r `can_be_split_into` (r, emp) /\ r `can_be_split_into` (emp, r)

// let test3 ()
// : RST nat r1 (fun _ -> r3)
//   (fun rm -> rm r1 == 2)
//   (fun rm_in x rm_out -> x == 2 /\ rm_out r3 > 2)
// = f1 0; f2 0; f3 3;
//   let x = rst_frame r3 (fun _ -> r3) r3 test1 in
//   rst_frame r3 (fun _ -> r3) r3 test1

// let test4 ()
// : RST unit r1 (fun _ -> r2)
//   (fun rm -> rm r1 == 2)
//   (fun rm_in x rm_out -> True)
// = f1 0; ()  //this works because the lift is parametric in the resource, else () would need to be wrapped in rst_frame

// // open FStar.Tactics

// // module T = FStar.Tactics

// // [@resolve_implicits]
// // let resolve_all_implicits () : Tac unit =
// //   T.dump "Remaining problems:"

// // assume val f_imp
// // : unit -> RST unit r1 (fun _ -> r1) (fun _ -> True) (fun _ _ _ -> True)
// // assume val g_imp
// // : unit -> RST unit r2 (fun _ -> r2) (fun _ -> True) (fun _ _ _ -> True)

// // let test_imp ()
// // : RST unit (r1 <*> r2) (fun _ -> r1 <*> r2)
// //   (fun _ -> True) (fun _ _ _ -> True)
// // = rst_frame _ #r1 #(fun _ -> r1) _ _ #(fun _ -> True) #(fun _ _ _ -> True) f_imp;
// //   rst_frame _ #r2 #(fun _ -> r2) _ _ #(fun _ -> True) #(fun _ _ _ -> True) g_imp


// /// Testing basic pattern matching


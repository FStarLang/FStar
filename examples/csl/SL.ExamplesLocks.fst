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
module SL.ExamplesLocks

open SL.Base
open SL.AutoTactic

let test_acq (r:ref int) (l:lock [ii r] (fun _ -> True)) : ST int (fun p m -> m == emp /\ (forall v. p 3 (r |> v))) [ii r]
  by (sl_auto ())
    
  =
  acquire l;
  3

let test_acq_rel (r:ref int) (l:lock [ii r] (fun _ -> True)) : ST unit (fun p m -> m == emp /\ p () emp) [] by (sl_auto ())
  =
  acquire l;
  let v = !r in
  release l

let set_and_ret (r:ref int) (l : lock [ii r] (fun _ -> True)) (n : nat) () : ST int (fun p m -> m == emp /\ p n emp) [] by (sl_auto ()) =
  acquire l;
  r := n;
  release l;
  n

(* Note: final heap is empty, it is the lock that owns `r` *)
let test06 (r:ref int) : ST int (fun p m -> exists v. m == r |> v /\ p 3 emp) [] by (sl_auto ()) =
  let l = mklock #(fun _ -> True) [ii r]  in
  let (x, y) = par (set_and_ret r l 1) (set_and_ret r l 2) in
  x + y

let test07 () : ST int (fun p m -> m == emp /\ (forall r. p 3 (r |> 5))) [] by (sl_auto ()) =
  let r = alloc 5 in
  3
  

let test08 (r : ref int) : ST int (fun p m -> exists v. m == (r |> v) /\ (forall r'. p v (r |> v <*> r' |> v))) [ii r] by (sl_auto ()) =
  let v = !r in
  let r' = alloc v in
  v
  
let test09 (r : ref int) : ST int (fun p m -> exists v. m == (r |> v) /\ (forall r'. p v (r' |> v <*> r |> v))) [ii r] by (sl_auto ()) =
  let v = !r in
  let r' = alloc v in
  v

let test10 () : ST int (fun p m -> m == emp /\ (forall i m. p i m)) [] by (sl_auto ()) =
  let r = alloc 3 in
  test08 r

let test11 () : ST unit (fun p m -> m == emp /\ p () emp) [] by (sl_auto ()) =
  let r = alloc 3 in
  r := 22;
  free r

let non_neg_inv (r:ref int) : memory -> Type0 =
  fun m -> exists v. v >= 0 /\ mem_eq (m == r |> v)

open FStar.Tactics

let take_and_incr (r:ref int) (l : lock [ii r] (fun m -> non_neg_inv r m)) : ST unit (fun p m -> m == emp /\ p () emp) [] by (sl_auto ()) =
  acquire l;
  r := !r + 1;
  release l

let test12 () : ST unit (fun p m -> m == emp /\ p () emp) [] by (sl_auto ()) =
  let r = alloc 0 in
  let l = mklock #(fun m -> non_neg_inv r m) [ii r] in
  ()

let test13 () : ST unit (fun p m -> m == emp /\ p () emp) [] by (sl_auto ()) =
  let r = alloc 0 in
  let l = mklock #(fun m -> non_neg_inv r m) [ii r] in
  acquire l;
  free r

let test14 () : ST unit (fun p m -> m == emp /\ p () emp) [] by (sl_auto ()) =
  let r = alloc 0 in
  let l = mklock #(fun m -> non_neg_inv r m) [ii r] in
  let _ = par (fun () -> take_and_incr r l) (fun () -> take_and_incr r l) in
  acquire l;
  free r

let test15 () : ST unit (fun p m -> m == emp /\ p () emp) [] by (sl_auto ()) =
  let r = alloc 0 in
  let l = mklock #(fun m -> non_neg_inv r m) [ii r] in
  let _ = par (fun () -> take_and_incr r l) (fun () -> take_and_incr r l) in
  acquire l;
  let v = !r in
  free r

let test16 () : ST unit (fun p m -> m == emp /\ p () emp) [] by (sl_auto ()) =
  let r = alloc 0 in
  let l = mklock #(fun m -> non_neg_inv r m) [ii r] in
  let _ = par (fun () -> take_and_incr r l) (fun () -> take_and_incr r l) in
  acquire l;
  let v = !r in
  assert (v >= 0);
  free r

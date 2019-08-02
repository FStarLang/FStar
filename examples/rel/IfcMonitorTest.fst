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
module IfcMonitorTest

open Label
open IfcMonitor
open FStar.DM4F.Heap.IntStoreFixed


(* Some test cases *)

let h0 = create 5
let env x = if x = to_id 3 || x = to_id 4 then High else Low

(* l1 := h1 *)
let p1 = Assign (to_id 1) (AVar (to_id 3))
let test1 = assert_norm (None? (interpret_com h0 p1 env Low))

(* l1 := l2 *)
let p2 = Assign (to_id 1) (AVar (to_id 2))
let test2 = assert_norm (Some? (interpret_com h0 p2 env Low))

(* If (h1 + 2 <> 0 then {l1 := 9}   [env0(h1) = 5] *)
let p3 = If (AOp Plus (AVar (to_id 3)) (AInt 2)) (Assign (to_id 1) (AInt 0)) Skip
let test3 = assert_norm (None? (interpret_com h0 p3 env Low))

(* This is example shows a difference to the type system*)
(* If (h1 - 5  <> 0 then {l1 := 0}  [env0(h1) = 5] *)
let p4 = If (AOp Plus (AVar (to_id 3)) (AInt (- 5))) (Assign (to_id 1) (AInt 0)) Skip
let test4 = assert_norm (Some? (interpret_com h0 p4 env Low))

(* h1 := h2; l2 := h1 *)
let p5 = Seq (Assign (to_id 3) (AVar (to_id 4))) (Assign (to_id 2) (AVar (to_id 3)))
let test5 = assert_norm (None? (interpret_com h0 p5 env Low))

(* This falis, as expected 
(* h1 := l1; l2 := h1 *)
let p6 = Seq (Assign (to_id 3) (AVar (to_id 1))) (Assign (to_id 2) (AVar (to_id 3)))
let test6 = assert_norm (Some? ((interpret_com h0 p6 Low)))
#reset-options
*)

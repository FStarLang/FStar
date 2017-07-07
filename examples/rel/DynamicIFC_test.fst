module DynamicIFC_test

open Label
open DynamicIFC
open FStar.DM4F.Heap.LabeledIntStoreFixed


(* Some test cases *)

let h0 = upd (upd (create (5,Low)) (to_id 3) (5, High)) (to_id 4) (5, High)

(* l1 := h1 *)
let p1 = Assign (to_id 1) (AVar (to_id 3))
let test1 = assert_norm (None? (interpret_com h0 p1 Low))

(* l1 := l2 *)
let p2 = Assign (to_id 1) (AVar (to_id 2))
let test2 = assert_norm (Some? (interpret_com h0 p2 Low))

(* If (h1 + 2 <> 0 then {l1 := 9}   [env0(h1) = 5] *)
let p3 = If (AOp Plus (AVar (to_id 3)) (AInt 2)) (Assign (to_id 1) (AInt 0)) Skip
let test3 = assert_norm (None? (interpret_com h0 p3 Low))

(* This is example shows the "weak" semantic of the monitor's security *)
(* If (h1 - 5  <> 0 then {l1 := 9}  [env0(h1) = 5] *)
let p4 = If (AOp Plus (AVar (to_id 3)) (AInt (- 5))) (Assign (to_id 1) (AInt 0)) Skip
let test4 = assert_norm (Some? (interpret_com h0 p4 Low))

(* h1 := h2; l2 := h1 *)
let p5 = Seq (Assign (to_id 3) (AVar (to_id 4))) (Assign (to_id 2) (AVar (to_id 3)))
let test5 = assert_norm (None? (interpret_com h0 p5 Low))

(* h1 := l1; l2 := h1 *)
let p6 = Seq (Assign (to_id 3) (AVar (to_id 1))) (Assign (to_id 2) (AVar (to_id 3)))
let test6 = assert_norm (Some? ((interpret_com h0 p6 Low)))
#reset-options


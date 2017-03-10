module IfcExampleReify1

open Rel
open WhileReify
open IfcRulesReify
open FStar.DM4F.Heap.IntStoreFixed
open FStar.DM4F.IntStoreExcFixed

(* (Warning) Top-level let-bindings must be total; this term may have effects *)

assume val x : id
assume val y : id
assume val z : id
assume val c : id

let env var = 
  if var = x then Low
  else if var = y then Low 
    else if var = c then Low
      else if var = z then High
        else High

(* 
  While c > 0{
    x := y; 
    y := y + 6;
    z := y + 7;
    x := z + 7;
    c := c - 1 
  }
*)

let c1_0 body = While (AVar c) body (AVar c)
let c1_1 = Assign x (AVar y)
let c1_2 = Assign y (AOp Plus (AVar x) (AInt 6))
let c1_3 = Assign z (AOp Plus (AVar y) (AInt 7))
let c1_4 = Assign x (AOp Plus (AVar z) (AInt 7))
let c1_5 = Assign c (AOp Minus (AVar c) (AInt 1))
let c1_6 = Seq c1_1 (Seq c1_2 (Seq (Seq c1_3 c1_4) c1_5))

let c1 = c1_0 c1_6

val c1_1_ni : unit -> Lemma (ni_com env c1_1 Low)
let c1_1_ni () = 
  avar_exp env y;
  assign_com env (AVar y) x

val c1_2_ni : unit -> Lemma (ni_com env c1_2 Low)
let c1_2_ni () = 
  avar_exp env x;
  aint_exp env 6;
  binop_exp env Plus (AVar x) (AInt 6) Low;
  assign_com env (AOp Plus (AVar x) (AInt 6)) y
  
val c1_5_ni : unit -> Lemma (ni_com env c1_5 Low)
let c1_5_ni () = 
  avar_exp env c;
  aint_exp env 1;
  binop_exp env Minus (AVar c) (AInt 1) Low;
  assign_com env (AOp Minus (AVar c) (AInt 1)) c

(* c1_4 cannot be shown to be non-interferent by typing since it contains an
   explicict flow from z (High) to x (Low)
   However, the sequence of c1_3 and c1_4 is fine, since in c1_3 we overwrite 
   z with the low value (y+7). 
   We can hence prove non-interference by relying on SMT.
   *)
#set-options "--z3rlimit 30"
val c1_3_4_ni : unit -> Lemma (ni_com env (Seq c1_3 c1_4) Low)
let c1_3_4_ni () = ()


#set-options "--z3rlimit 5"
val c1_6_ni : unit -> Lemma (ni_com env c1_6 Low)
let c1_6_ni () = 
  c1_3_4_ni ();
  c1_5_ni ();
  seq_com env (Seq c1_3 c1_4) c1_5 Low;
  c1_2_ni ();
  seq_com env c1_2 (Seq (Seq c1_3 c1_4) c1_5) Low;
  c1_1_ni ();
  seq_com env c1_1 (Seq c1_2 (Seq (Seq c1_3 c1_4) c1_5)) Low

val c1_ni : unit -> Lemma (ni_com env c1 Low)
let c1_ni () = 
  avar_exp env c;
  c1_6_ni ();
  while_com env (AVar c) c1_6 (AVar c) Low

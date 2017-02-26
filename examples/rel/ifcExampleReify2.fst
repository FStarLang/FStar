module IfcExampleReify2

open WhileReify
open IfcReify
open IfcTypechecker
open FStar.DM4F.Heap.IntStoreFixed
open FStar.DM4F.Exceptions

assume val hi : id
assume val lo : id
assume val c : id

let env var = 
  if var = hi then Low
  else if var = lo then Low
    else if var = c then High
      else High

(* 
  While c > 0{
    hi := lo + 1
    lo := hi + 1 
    c := c - 1 
  }
*)

let c_1 body = While (AVar c) body (AVar c)
let c_2 = Assign hi (AOp Plus (AVar lo) (AInt 1))
let c_3 = Assign lo (AOp Plus (AVar hi) (AInt 1))
let c_4 = Assign c (AOp Minus (AVar c) (AInt 1))
let c_body =  Seq (Seq c_2 c_3) c_4 

let cmd = c_1 c_body

#set-options "--z3rlimit 30"
val c_2_3_ni : unit -> Lemma (ni_com env (Seq c_2 c_3) Low)
let c_2_3_ni () = ()


#set-options "--z3rlimit 5"
val cmd_ni : unit -> 
  Exn label (requires True) (ensures fun ol -> Inl? ol ==> ni_com env cmd (Inl?.v ol))
let cmd_ni () = 
  c_2_3_ni ();
  tc_com_hybrid env cmd [Seq c_2 c_3, Low] 

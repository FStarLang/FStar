module IFC.Example1
open Distinct
open IFC.IFC
open FStar.Comp
open FStar.Relational

(* Fails iff label b > label a *)
let a = new_labeled_int 1
let b = new_labeled_int 0

assume Distinct : distinct2 a b

let test () = (if !b <> 0 then
                 a := 1
               else
                 a := 2);
               b := 0

(* Brute Force Approach *)
val test_ni : ni
let test_ni _ = compose2_self test tu

(* Following the typing derivation *)

(* !b : 0 *)
val ni_exp_deref_b : ni_exp 0
let ni_exp_deref_b tu = (deref_exp b) tu

(* 1 : bot *)
val ni_exp_1 : ni_exp bot
let ni_exp_1 tu = (const_exp 1) tu

(* 1 : 1 *)
val ni_exp_1' : ni_exp 1
let ni_exp_1' = sub_exp bot 1 ni_exp_1

(* 1 |- a := 1 *)
val ni_com_a_1: ni_com 1
let ni_com_a_1 tu = (assign_com a ni_exp_1') tu

(* 0 |- a := 1 *)
val ni_com_a_1': ni_com 0
let ni_com_a_1' tu = (sub_com 1 0  ni_com_a_1) tu

(* 2 : bot *)
val ni_exp_2 : ni_exp bot
let ni_exp_2 tu = (const_exp  2) tu

(* 2 : 1 *)
val ni_exp_2' : ni_exp 1
let ni_exp_2' = sub_exp bot 1 ni_exp_2

(* 1 |- a := 2 *)
val ni_com_a_2: ni_com 1
let ni_com_a_2 tu = (assign_com a ni_exp_2') tu

(* 0 |- a := 2 *)
val ni_com_a_2': ni_com 0
let ni_com_a_2' tu = (sub_com 1 0 ni_com_a_2) tu

(* 0 |- if (!b <> 0) then a := 1 else a := 2 *)
val ni_com_cond : ni_com 0
let ni_com_cond = cond_com 0 ni_exp_deref_b ni_com_a_1' ni_com_a_2'

(* bot |- if (!b <> 0) then a := 1 else a := 2 *)
val ni_com_cond' : ni_com bot
let ni_com_cond' = sub_com 0 bot ni_com_cond

(* 2 : bot *)
val ni_exp_0 : ni_exp bot
let ni_exp_0 tu = (const_exp 0) tu

(* 2 : 0 *)
val ni_exp_0' : ni_exp 0
let ni_exp_0' = sub_exp bot 0 ni_exp_0

(* 0 |- b := 0 *)
val ni_com_b : ni_com 0
let ni_com_b tu = (assign_com b ni_exp_0') tu

(* bot |- b := 0 *)
val ni_com_b' : ni_com bot
let ni_com_b' tu = (sub_com 0 bot ni_com_b) tu

(* bot |- if (!b <> 0) then a := 1 else a := 2; b := 0 *)
val ni_com_seq : ni_com bot
let ni_com_seq tu = (seq_com bot ni_com_cond' ni_com_b') tu

(* Noninterference result for the complete program *)
val ni_programm : ni
let ni_programm tu = ni_com_seq tu


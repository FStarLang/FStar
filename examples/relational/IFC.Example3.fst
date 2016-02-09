module IFC.Example3
open IFC.IFC
open FStar.Comp
open FStar.Relational
open Distinct

assume val la : label
assume val lb : lb:label{lb <= la}
assume val lc : lc:label{lc <= la}

let a = new_labeled_int la
let b = new_labeled_int lb
let c = new_labeled_int lc

assume Distinct : distinct3 a b c

let test () = a:= !b + !c

(* Brute Force Approach *)
val test_ni : ni
let test_ni _ = compose2_self test tu

(* Following the typing derivation *)

(* !b : lb *)
val ni_exp_deref_b : ni_exp lb
let ni_exp_deref_b tu = (deref_exp b) tu

(* !b : la *)
val ni_exp_deref_b' : ni_exp la
let ni_exp_deref_b' tu = (sub_exp lb la ni_exp_deref_b) tu

(* !c : lc *)
val ni_exp_deref_c : ni_exp lc
let ni_exp_deref_c tu = (deref_exp c) tu

(* !c : la *)
val ni_exp_deref_c' : ni_exp la
let ni_exp_deref_c' tu = (sub_exp lc la ni_exp_deref_c) tu

(* !b + !c : la *)
val ni_exp_a : ni_exp la
let ni_exp_a tu = (bin_op_exp la ni_exp_deref_b' ni_exp_deref_c') tu

(* la |- a := !b + !c *)
val ni_com_a: ni_com la
let ni_com_a tu = (assign_com a ni_exp_a) tu

(* bot |- a := !b + !c *)
val ni_com_a': ni_com bot
let ni_com_a' tu = (sub_com la bot ni_com_a) tu

(* Noninterference result for the complete program *)
val ni_program : ni
let ni_program tu = ni_com_a' tu


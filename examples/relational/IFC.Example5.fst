module IFC.Example5
open IFC.IFC
open FStar.Comp
open FStar.Relational
open FStar.Heap
open Distinct

assume val la : label
assume val lb : lb:label{lb >= la}
assume val lc : lc:label

let a = new_labeled_int la
let b = new_labeled_int lb
let c = new_labeled_int lc

assume Distinct : distinct3 a b c

(* This val-declaration is necessary (otherwise: FStar does not infer ST, but ALL) *)
val loop : unit -> ST unit (requires (fun _ -> True))
                           (ensures  (fun h r h' -> ((sel h a) = 0 ==> equal h h')
                                                 /\ ((sel h a) <> 0  ==> equal h' (upd (upd h b ((sel h b) + (sel h a))) a 0))))
let rec loop () = if !a <> 0 then (a := !a + -1; b := !b + 1; loop ())

let test () = loop ();
              c := 0

(* Brute Force Approach *)
val test_ni : ni
let test_ni _ = compose2_self test tu

(* Following the typing derivation *)

(* !a : la *)
val ni_exp_deref_a : ni_exp la
let ni_exp_deref_a tu = (deref_exp a) tu

(* -1 : bot *)
val ni_exp__1 : ni_exp bot
let ni_exp__1 tu = (const_exp (-1)) tu

(* -1 : la *)
val ni_exp__1a : ni_exp la
let ni_exp__1a tu = (sub_exp bot la ni_exp__1) tu

(* !a + -1 : la *)
val ni_exp_a : ni_exp la
let ni_exp_a tu = (bin_op_exp la ni_exp_deref_a ni_exp__1a) tu

(* la |- a := !a + -1  *)
val ni_com_a : ni_com la
let ni_com_a tu = (assign_com a ni_exp_a) tu

(* !b : lb *)
val ni_exp_deref_b : ni_exp lb
let ni_exp_deref_b tu = (deref_exp b) tu

(* 1 : bot *)
val ni_exp_1 : ni_exp bot
let ni_exp_1 tu = (const_exp 1) tu

(* 1 : lb *)
val ni_exp_1b : ni_exp lb
let ni_exp_1b tu = (sub_exp bot lb ni_exp_1) tu

(* !b + 1 : lb *)
val ni_exp_b : ni_exp lb
let ni_exp_b tu = (bin_op_exp lb ni_exp_deref_b ni_exp_1b) tu

(* lb |- !b + 1 *)
val ni_com_b : ni_com lb
let ni_com_b tu = (assign_com b ni_exp_b) tu

(* la |- !b + 1 *)
val ni_com_b' : ni_com la
let ni_com_b' tu = (sub_com lb la ni_com_b) tu

(* la |- a := !a + -1; b := !b + 1 *)
val ni_com_loop_body : ni_com la
let ni_com_loop_body tu = (seq_com la ni_com_a ni_com_b') tu

(* la |- while !a <> 0 {a := !a + -1; b := !b + 1} *)
val ni_com_loop : ni_com la
let ni_com_loop tu = (loop_com la ni_exp_deref_a ni_com_loop_body) tu

(* bot |- while !a <> 0 {a := !a + -1; b := !b + 1} *)
val ni_com_loop' : ni_com bot
let ni_com_loop' tu = (sub_com la bot ni_com_loop) tu

(* 0 : bot *)
val ni_exp_0 : ni_exp bot
let ni_exp_0 tu = (const_exp 0) tu

(* 0 : lc *)
val ni_exp_0' : ni_exp lc
let ni_exp_0' tu = (sub_exp bot lc ni_exp_0) tu

(* lc |- c := 0 *)
val ni_com_c : ni_com lc
let ni_com_c tu = (assign_com c ni_exp_0') tu

(* bot |- c := 0 *)
val ni_com_c' : ni_com bot
let ni_com_c' tu = (sub_com lc bot ni_com_c) tu

(* Noninterference for the complete program *)
val ni_program : ni
let ni_program tu = (seq_com bot ni_com_loop' ni_com_c') tu

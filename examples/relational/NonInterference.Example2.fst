module NonInterference.Example2
open NonInterference.NI
open FStar.Comp
open FStar.Relational
open Distinct

(* Fails iff label c < (max (label a) (label b) *)
let a = new_labeled_int 1
let b = new_labeled_int 0
let c = new_labeled_int 2

assume Distinct : distinct3 a b c

let test () = c := !a + !b;
              if !c < !a then
                b := 0
              else
                b := 1;
              a := 0

val test_ni : ni
let test_ni _ = compose2_self test tu


(* Simple Examples using the above definition of Noninterference*)
module NonInterference.Example1
open NonInterference.NI
open FStar.Comp
open FStar.Relational
open Distinct

(* Fails iff label b > label a *)
let a = new_labeled_int 1
let b = new_labeled_int 0


assume Distinct : distinct2 a b

let test () = (if !b = 0 then
                 a := 2
               else
                 a := 1);
               b := 0

val test_ni : ni
let test_ni _ = compose2_self test tu


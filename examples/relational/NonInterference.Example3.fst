module NonInterference.Example3
open NonInterference.NI
open FStar.Comp
open FStar.Relational
open Distinct

assume val la : int
assume val lb : lb:int{lb <= la}
assume val lc : lc:int{lc <= la}

let a = new_labeled_int la
let b = new_labeled_int lb
let c = new_labeled_int lc

assume Distinct : distinct3 a b c

let test () = a:= !b + !c

val test_ni : ni
let test_ni _ = compose2_self test tu


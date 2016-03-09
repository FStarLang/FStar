module NonInterference.Example5
open NonInterference.NI
open FStar.Comp
open FStar.Relational
open FStar.Heap
open Distinct

assume val la : int
assume val lb : lb:int{lb >= la}
assume val lc : lc:int

let a = new_labeled_int la
let b = new_labeled_int lb
let c = new_labeled_int lc

assume Distinct : distinct3 a b c

val loop : unit -> ST unit (requires (fun _ -> True))
                           (ensures  (fun h r h' -> ((sel h a) <= 0 ==> equal h h')
                                                 /\ ((sel h a) > 0  ==> equal h' (upd (upd h b ((sel h b) + (sel h a))) a 0))))
let rec loop _ = if !a > 0 then (a := !a - 1; b := !b + 1; loop ())

val loop' : unit -> ST unit (requires (fun _ -> True))
                            (ensures  (fun h r h' -> ((sel h a) <= 0 ==> equal h h')
                                                  /\ ((sel h a) > 0  ==> False)))
let rec loop' _ = if !a > 0 then (a := !a + 1; b := !b + 1; loop' ())

let test () = loop ();
              c := 0;
              loop' ();
              c := 1

val test_ni : ni
let test_ni _ = compose2_self test tu

let test' () = a := 1249;
               loop ();
               c := !b;
               a := !a + 1;
               loop' ();
               c := !b

val test_ni' : ni
let test_ni' _ = compose2_self test' tu


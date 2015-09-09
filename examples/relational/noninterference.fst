(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:set.fsi heap.fst st.fst all.fst st2.fst
  --*)

module NonInterference

open FStar.Comp
open FStar.Heap
open FStar.Relational

(* We model labels with different levels as integers *)
type label = int 

(* Label of the attacker *)
assume val alpha : label

(* Labeling function (assigns a label to every reference) *)
assume val label_fun : ref int -> Tot label

(* A reference can be observed bu the attacker if its label is not higher than 
   alpha *)
let attacker_observable x = label_fun x <= alpha

(* Definition of Noninterference  If all attacker-observable references contain
   equal values before the function call, then they also have to contain equal
   values after the function call. *)
type ni = unit ->
          ST2 (rel unit unit)
              (requires (fun h2 -> (forall (x:ref int). 
                                        attacker_observable x 
                                        ==> sel (R.l h2) x = sel (R.r h2) x)))
              (ensures  (fun _ _ h2 -> (forall (x:ref int).
                                        attacker_observable x 
                                        ==> sel (R.l h2) x = sel (R.r h2) x)))

(* Function to create new labeled references *)
assume val new_labeled_int : l:label -> x:ref int{label_fun x = l}


(* Simple Examples using the above definition of Noninterference*)
module Example1
open NonInterference
open FStar.Comp
open FStar.Relational

(* Fails iff label b > label a *)
let a = new_labeled_int 1
let b = new_labeled_int 0


assume Distinct : a <> b

let test () = (if !b = 0 then
                 a := 2
               else
                 a := 1);
               b := 0

val test_ni : ni
let test_ni () = compose2_self test (twice ())

module Example2
open NonInterference
open FStar.Comp
open FStar.Relational

(* Fails iff label c < (max (label a) (label b) *)
let a = new_labeled_int 1
let b = new_labeled_int 0
let c = new_labeled_int 2

assume Distinct : a <> b /\ a <> c /\ b <> c

let test () = c := !a + !b;
              if !c < !a then
                b := 0
              else 
                b := 1;
              a := 0

val test_ni : ni
let test_ni () = compose2_self test (twice ())


module Example3
open NonInterference
open FStar.Comp 
open FStar.Relational

assume val la : int 
assume val lb : lb:int{lb <= la}
assume val lc : lc:int{lc <= la} 

let a = new_labeled_int la
let b = new_labeled_int lb
let c = new_labeled_int lc

assume Distinct : a <> b /\ a <> c /\ b <> c

let test () = a:= !b + !c

val test_ni : ni
let test_ni () = compose2_self test (twice ())


module Example4
open NonInterference
open FStar.Comp 
open FStar.Relational

assume val la : int 
assume val lb : lb:int{lb >= la}
assume val lc : lc:int{lc >= la} 

let a = new_labeled_int la
let b = new_labeled_int lb
let c = new_labeled_int lc

assume Distinct : a <> b /\ a <> c /\ b <> c

let test () = if !a = 0 then
                b := 1
              else
                c := 2

val test_ni : ni
let test_ni () = compose2_self test (twice ())


module Example5
open NonInterference
open FStar.Comp 
open FStar.Relational
open FStar.Heap

assume val la : int 
assume val lb : lb:int{lb >= la}
assume val lc : lc:int

let a = new_labeled_int la
let b = new_labeled_int lb
let c = new_labeled_int lc

assume Distinct : a <> b /\ a <> c /\ b <> c

(* This val-declaration is necessary (otherwise: FStar does not infer ST, but ALL) *)
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
let test_ni () = compose2_self test (twice ())

(* This val-declaration is necessary (otherwise: Stackoverflow) *)
val test' : unit -> St (u:unit{False})
let test' () = a := 1249;
               loop ();
               c := !b;
               a := !a + 1;
               loop' ();
               c := !b

val test_ni' : ni
let test_ni' () = compose2_self test' (twice ())

(*--build-config
    options:--admit_fsi FStar.Set;
    variables:LIB=../../lib;
    other-files:$LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/st2.fst
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

let test () = c := !a + !b;
              if !c < !a then
                b := 0
              else 
                b := 1;
              a := 0

val test_ni : ni
let test_ni () = compose2_self test (twice ())

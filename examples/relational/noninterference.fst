(*--build-config
    options:--admit_fsi FStar.Set --z3timeout 15 --eager_inference;
    other-files:set.fsi heap.fst st.fst all.fst st2.fst distinct.fst
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

type alpha_equiv (h:double heap) = (forall (x:ref int). attacker_observable x 
                                                   ==> eq_irel (sel_rel1 h x))

(* Definition of Noninterference  If all attacker-observable references contain
   equal values before the function call, then they also have to contain equal
   values after the function call. *)
type ni = double unit ->
          ST2 (double unit)
              (requires (fun h -> alpha_equiv h))
              (ensures  (fun _ _ h2 -> alpha_equiv h2))

(* Function to create new labeled references *)
assume val new_labeled_int : l:label -> x:ref int{label_fun x = l}

(* Simple Examples using the above definition of Noninterference*)
module Example1
open NonInterference
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

module Example2
open NonInterference
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

module Example3
open NonInterference
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

module Example4
open NonInterference
open FStar.Comp
open FStar.Relational
open Distinct

assume val la : int
assume val lb : lb:int{lb >= la}
assume val lc : lc:int{lc >= la}

let a = new_labeled_int la
let b = new_labeled_int lb
let c = new_labeled_int lc

assume Distinct : distinct3 a b c

let test () = if !a = 0 then
                b := 1
              else
                c := 2

val test_ni : ni
let test_ni _ = compose2_self test tu

module Example5
open NonInterference
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

(* The follwogin two examples are left commented due to #389 *)
(* --eager_inference seems to help but they still take up to 4GB of memory*)

(*
(* These examples require a lot of memory *)
module Example6
open NonInterference
open FStar.Comp
open FStar.Relational
open Distinct

assume val la : la:int
assume val lb : lb:int{lb <= la}
assume val lc : lc:int{lc <= la /\ lb <= lc}
assume val ld : ld:int
assume val le : le:int{le <= ld /\ le <= lc}
assume val lf : lf:int{lf <= ld /\ le <= lf}
assume val lg : lg:int
assume val lh : lh:int{lh <= lg}
assume val li : li:int{li <= lg}
assume val lj : lj:int

let a = new_labeled_int la
let b = new_labeled_int lb
let c = new_labeled_int lc
let d = new_labeled_int ld
let e = new_labeled_int le
let f = new_labeled_int lf
let g = new_labeled_int lg
let h = new_labeled_int lh
let i = new_labeled_int li
let j = new_labeled_int lj

assume Distinct : distinct10 a b c d e f g h i j

let test () = a := !b + !c;
              d := !e * !f;
              c := !a - !e;
              g := !h + !i;
              f := !a + !b + !c + !d + !e + !g + !h + !i + !j;
              f := !f - !a - !b - !c - !d;
              f := !f - !e - !g - !h - !i - !j;
              if !f = 0 then
                f := !e
              else
                f := !a

val test_ni : ni
let test_ni _ = compose2_self test tu

(* Module 6 and 7 both verify indidually, but do not verify both at the same
   time, as memory is not freed in between *)
(* The same program manually composed (Way slower) *)
module Example7
open NonInterference
open FStar.Comp
open FStar.Relational
open FStar.RelationalState
open Distinct

assume val la : la:int
assume val lb : lb:int{lb <= la}
assume val lc : lc:int{lc <= la /\ lb <= lc}
assume val ld : ld:int
assume val le : le:int{le <= ld /\ le <= lc}
assume val lf : lf:int{lf <= ld /\ le <= lf}
assume val lg : lg:int
assume val lh : lh:int{lh <= lg}
assume val li : li:int{li <= lg}
assume val lj : lj:int

let a = new_labeled_int la
let b = new_labeled_int lb
let c = new_labeled_int lc
let d = new_labeled_int ld
let e = new_labeled_int le
let f = new_labeled_int lf
let g = new_labeled_int lg
let h = new_labeled_int lh
let i = new_labeled_int li
let j = new_labeled_int lj

assume Distinct : distinct10 a b c d e f g h i j
(* op_Hat_Minus does not work... *)
let op_Hat_At = rel_map2T (fun x y -> x - y)

val test_ni : ni
let test_ni _ =
  let _ = assign_rel1 a ((read_rel1 b) ^+ (read_rel1 c)) in
  let _ = assign_rel1 d ((read_rel1 d) ^* (read_rel1 f)) in
  let _ = assign_rel1 c ((read_rel1 a) ^@ (read_rel1 c)) in
  let _ = assign_rel1 g ((read_rel1 h) ^+ (read_rel1 i)) in
  let _ = assign_rel1 g ((read_rel1 h) ^+ (read_rel1 i)) in
  let _ = assign_rel1 f ((read_rel1 a) ^+ (read_rel1 b)
                             ^+ (read_rel1 c) ^+ (read_rel1 d)
                             ^+ (read_rel1 e) ^+ (read_rel1 g)
                             ^+ (read_rel1 h) ^+ (read_rel1 i)
                             ^+ (read_rel1 j)) in
  let _ = assign_rel1 f ((read_rel1 f) ^@ (read_rel1 a)
                             ^@ (read_rel1 b) ^@ (read_rel1 c)
                             ^@ (read_rel1 d) ^@ (read_rel1 e)
                             ^@ (read_rel1 g) ^@ (read_rel1 h)
                             ^@ (read_rel1 i) ^@ (read_rel1 j)) in
  match (eq_rel (read_rel1 f) (R 0 0)) with
  | R true true   -> assign_rel1 f (read_rel1 e)
  | R false false -> assign_rel1 f (read_rel1 a)
*)

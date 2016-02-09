(* The follwogin two examples are left commented due to #389 *)
(* --eager_inference seems to help but they still take up to 4GB of memory*)
(* These examples require a lot of memory *)
module NonInterference.Example6
open NonInterference.NI
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


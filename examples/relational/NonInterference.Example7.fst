(* Module 6 and 7 both verify indidually, but do not verify both at the same
   time, as memory is not freed in between *)
(* The same program manually composed (Way slower) *)
module NonInterference.Example7
open NonInterference.NI
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

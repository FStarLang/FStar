module St_Rel
open Rel
open FStar.Heap

(* Pure relational reasoning about stateful functions *)

  (* Pure functions using heap passing *)
val f1_hp : heap -> ref int -> Tot (heap * int)
let f1_hp h x = h, sel h x

val f2_hp : heap -> ref int -> Tot (heap * int)
let f2_hp h x = h, 0

  (* Stateful functions ipmlementing these pure functions *)
val f1 : x:(ref int) -> ST int (requires (fun h -> True))
                               (ensures  (fun h r h' -> fst (f1_hp h x) = h'
                                                     /\ snd (f1_hp h x) = r))
let f1 x = !x

val f2 : x:(ref int) -> ST int (requires (fun h -> True))
                               (ensures  (fun h r h' -> fst (f2_hp h x) = h'
                                                     /\ snd (f2_hp h x) = r))
let f2 x = 0

  (* Proving relational properties using pure lemmas *)
val f1_ni : h:(eq heap) -> x:(eq (ref int)) 
    -> Lemma (b2t (r_eq (lift snd (lift2 f1_hp h x))))
let f1_ni h x = ()

val f2_ni : h:(rel heap) -> x:(rel (ref int)) 
    -> Lemma (b2t (r_eq (lift snd (lift2 f2_hp h x))))
let f2_ni h x = ()

(* EXPECT 32 FAILURES *)
(* ******************************************************************************** *)
module Neg

assume val g : 'a -> Tot 'b
assume val h : a:Type -> b:Type -> a:'a -> Tot (b:'b{b == g a})
assume val length: list 'a -> Tot int

opaque val x:nat
let x = -1 //should fail reporting 1 error
opaque val y:nat
let y = -1 //should also fail reporting only 1 error

let assert_0_eq_1 () = assert (0=1) //should fail

let hd_int_inexhaustive l = match l with
  | hd::_ -> hd //should fail

val test_label: x:int -> Pure int (requires (x > 0)) (ensures (fun y -> y > 0))
let test_label x = x

val test_precondition_label: x:int -> Tot int
let test_precondition_label x = test_label x //should fail

val test_postcondition_label: x:int -> Pure int (requires True) (ensures (fun y -> y > 0))
let test_postcondition_label x = x //should fail

val bad_projector: option 'a -> 'a
let bad_projector x = Some.v x (* should fail *)

assume type T : (result int -> Type) -> Type
assume TEST: T (fun ri -> b2t (V.v ri = 0))//should fail: not (is_V ri)

assume val f1: (x:int -> Tot unit) -> Tot unit
assume val g1: nat -> Tot unit
let h1 = f1 (fun x -> g1 x) //should fail; x is not nat


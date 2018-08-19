module NegativeTests.Neg

irreducible val x:nat
[@(expect_failure [19])]
let x = -1 //should fail reporting 1 error
irreducible val y:nat
[@(expect_failure [19])]
let y = -1 //should also fail reporting only 1 error

[@(expect_failure [19])]
let assert_0_eq_1 () = assert (0=1) //should fail

[@(expect_failure [19])]
let hd_int_inexhaustive l = match l with
  | hd::_ -> hd //should fail

val test_label: x:int -> Pure int (requires (b2t (x > 0))) (ensures (fun y -> y > 0))
let test_label x = x

val test_precondition_label: x:int -> Tot int
[@(expect_failure [19])]
let test_precondition_label x = test_label x //should fail

val test_postcondition_label: x:int -> Pure int (requires True) (ensures (fun y -> y > 0))
[@(expect_failure [19])]
let test_postcondition_label x = x //should fail

val bad_projector: option 'a -> 'a
[@(expect_failure [19])]
let bad_projector x = Some?.v x (* should fail *)

assume type t_pred : (result int -> Type) -> Type
[@(expect_failure [19])]
assume val test: t_pred (fun ri -> b2t (V?.v ri = 0))//should fail: not (V? ri)

assume val f1: (x:int -> Tot unit) -> Tot unit
assume val g1: nat -> Tot unit
[@(expect_failure [19])]
let h1 = f1 (fun x -> g1 x) //should fail; x is not nat

assume type phi_1510 :Type0
[@(expect_failure [309])]
type t (a:Type) :(_:Type0{phi_1510})=
  | C: x:a -> t a

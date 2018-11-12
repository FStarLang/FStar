module NegativeTests.Bug260
type pnat =
  | O : pnat
  | S : pnat -> pnat

type validity : n:pnat -> Type =
  | VSucc : n:pnat -> Tot (validity (S n))
val bad : t:pnat -> Tot (validity (S (S t)))

[@(expect_failure [19])]
let bad t = VSucc t


(* Hard to keep this one in the suite since the program fails to even --lax check *)
(* module EscapingVariable *)
(* assume type Good : int -> Type *)
(* assume val enc: plain:int -> c:unit{Good plain} *)
(* assume val repr : int -> int *)

(* let f (text:int) = enc (repr text) //should fail; plain escapes *)

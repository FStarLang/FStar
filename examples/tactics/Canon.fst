module Canon

open FStar.Tactics
open FStar.Tactics.Canon

assume val x : int
assume val y : int
assume val z : int

let lem1 = assert_by_tactic (dump "BEFORE";; canon;; dump "AFTER") ((x + y) * (z + z) == 2 * z * (y + x))

(* let lem2 = assert_by_tactic (dump "BEFORE";; tau;; dump "AFTER") (x == x) *)

let lemma_mul_5 (a b c d e : int) =
    assert_by_tactic
        (dump "BEFORE";; canon;; dump "AFTER")
        ((a+b+c+d+e)*(a+b+c+d+e) ==
                a * a + a * b + a * c + a * d + a * e
              + b * a + b * b + b * c + b * d + b * e
              + c * a + c * b + c * c + c * d + c * e
              + d * a + d * b + d * c + d * d + d * e
              + e * a + e * b + e * c + e * d + e * e)

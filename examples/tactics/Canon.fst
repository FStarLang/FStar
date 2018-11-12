module Canon

open FStar.Tactics
open FStar.Tactics.Canon
open FStar.Mul

assume val w : int
assume val x : int
assume val y : int
assume val z : int

// Testing the canonizer, it should be the only thing needed for this file
let check_canon () =
    canon ();
    or_else qed
            (fun () -> dump "`canon` left the following goals";
                       fail "")

let lem0 =  assert_by_tactic (x * (y * z) == (x * y) * z) check_canon
let lem0' = assert_by_tactic (w * (x * (y * z)) == ((z * y) * x) * w) check_canon

// TODO: for now, canon is not enough as we don't collect factors, so we
// leave the rest to the SMT
let lem1 =
    assert_by_tactic ((x + y) * (z + z) == 2 * z * (y + x))
                     canon

let lem2 (x : int) =
    assert_by_tactic (2 + x + 3 * 8 == x + 26)
                     check_canon

let lem3 (a b c d e : int) =
    assert_by_tactic (c + (b + a) == b + (a + c))
                     check_canon

let lem3_nat (a b c d e : (x:nat{0 <= x /\ x < 256})) =
    assert_by_tactic (c + (b + a) == b + (a + c))
                     check_canon

let lem4 (a b c : int) =
    assert_by_tactic ((a+c+b)*(b+c+a) == a * a + (((b+c)*(c+b) + a * (b+c)) + c*a) + b*a)
                     check_canon

(* The following tests should pass, but it's too slow to run them on every regression build, *)
(* and the previous ones are probably enough *)

let lem5 (a b c d e : int) =
    assert_by_tactic
        ((a+b+c+d+e)*(a+b+c+d+e) ==
                a * a + a * b + a * c + a * d + a * e
              + b * a + b * b + b * c + b * d + b * e
              + c * a + c * b + c * c + c * d + c * e
              + d * a + d * b + d * c + d * d + d * e
              + e * a + e * b + e * c + e * d + e * e)
        check_canon

let lem6 (a b c d e : int) =
    assert_by_tactic
        ((a+b+c+d+e)*(e+d+c+b+a) ==
                a * a + a * b + a * c + a * d + a * e
              + b * a + b * b + b * c + b * d + b * e
              + c * a + c * b + c * c + c * d + c * e
              + d * a + d * b + d * c + d * d + d * e
              + e * a + e * b + e * c + e * d + e * e)
        check_canon

let lem7 (a b c d : int) =
    assert_by_tactic
        ((a+b+c+d)*(b+c+d+a) ==
                a * a
              + b * b
              + c * c
              + d * d
              + a * b + a * b
              + a * c + a * c
              + a * d + a * d
              + b * c + b * c
              + b * d + b * d
              + c * d + c * d)
        check_canon

let lem8 (a b c d : int) =
    assert_norm (1 * 1 == 1);
    assert_by_tactic ((a * b) * (c * d) == d * b * c * a)
                     check_canon

let lem9 (n:int) (p:int) (r:int) (h:int) (r0:int) (r1:int) (h0:int) (h1:int) (h2:int) (s1:int) (d0:int) (d1:int) (d2:int) (hh:int) =
    assert_by_tactic (((h2 * (n * n) + h1 * n + h0) * (r1*n + r0)) =
                        ((h2 * r1) * (n * n * n) + (h2 * r0 + h1 * r1) * (n * n) + (h1 * r0 + h0 * r1) * n + h0 * r0))
                     check_canon

// Takes long, around a minute
(* let lem10 (a b c : int) (n:int) (p:int) (r:int) (h:int) (r0:int) (r1:int) (h0:int) (h1:int) (h2:int) (s1:int) (d0:int) (d1:int) (d2:int) (hh:int) = *)
(*     assert_by_tactic ((((h2 * (n * n) + h1 * n + h0) * (r1*n + r0))) * ((a+b+c)*(a+b+c)) = *)
(*                         (((h2 * r1) * (n * n * n) + (h2 * r0 + h1 * r1) * (n * n) + (h1 * r0 + h0 * r1) * n + h0 * r0)) *)
(*                         * (a * a + a * b + a * c +  b * a + b * b + b * c + c * a + c * b + c * c)) *)
(*                      check_canon *)

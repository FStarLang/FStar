module Canon

open FStar.Tactics
open FStar.Tactics.Canon

assume val x : int
assume val y : int
assume val z : int

// Testing the canonizer, it should be the only thing needed for this file
let check_canon =
    canon;;
    (* eg <-- cur_goal; *)
    (* let (_, g), _ = eg in *)
    (* print ("After canonizing: " ^ term_to_string g);; *)
    trefl;;
    tdone

let lem0 = assert_by_tactic check_canon (x * (y * z) == (x * y) * z)

// TODO: for now, canon is not enough as we don't collect factors
let lem1 =
    assert_by_tactic canon ((x + y) * (z + z) == 2 * z * (y + x))

let lem2 (x : int) =
    assert_by_tactic check_canon (2 + x + 3 * 8 == x + 26)

let lem3 (a b c d e : int) =
    assert_by_tactic check_canon (c + (b + a) == b + (a + c))

let lem4 (a b c : int) =
    assert_by_tactic check_canon ((a+c+b)*(b+c+a) == a * a + (((b+c)*(c+b) + a * (b+c)) + c*a) + b*a)

let lem5 (a b c d e : int) =
    assert_by_tactic check_canon
        ((a+b+c+d+e)*(a+b+c+d+e) ==
                a * a + a * b + a * c + a * d + a * e
              + b * a + b * b + b * c + b * d + b * e
              + c * a + c * b + c * c + c * d + c * e
              + d * a + d * b + d * c + d * d + d * e
              + e * a + e * b + e * c + e * d + e * e)

let lem6 (a b c d e : int) =
    assert_by_tactic check_canon
        ((a+b+c+d+e)*(e+d+c+b+a) ==
                a * a + a * b + a * c + a * d + a * e
              + b * a + b * b + b * c + b * d + b * e
              + c * a + c * b + c * c + c * d + c * e
              + d * a + d * b + d * c + d * d + d * e
              + e * a + e * b + e * c + e * d + e * e)

let lem7 (a b c d : int) =
    assert_by_tactic check_canon
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

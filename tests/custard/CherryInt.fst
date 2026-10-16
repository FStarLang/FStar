module CherryInt
module U32 = FStar.UInt32

let rec fact (n: nat) : nat = if n = 0 then 1 else n * fact (n - 1)

let rec sum (l: list int) : int =
  match l with
  | [] -> 0
  | x :: tl -> x + sum tl

let rec range (lo: int) (n: nat) : Tot (list int) (decreases n) =
  if n = 0 then [] else lo :: range (lo + 1) (n - 1)

let div_ok (a: int) (b: nonzero) (q r: int) : bool = a / b = q && a % b = r

let main () : U32.t =
  let f30 = fact 30 in
  let big = 265252859812191058636308480000000 in
  let ok_fact = f30 = big && f30 / fact 28 = 870 && f30 % 1000000007 = 109361473 in
  let ok_div =
    div_ok 7 2 3 1 && div_ok (-7) 2 (-4) 1 && div_ok 7 (-2) (-3) 1 &&
    div_ok (-7) (-2) 4 1 &&
    div_ok (- (fact 25)) 7 (-2215887149047283712000000) 0 &&
    div_ok (- (fact 25) - 1) 1000000000000 (-15511210043331) 14015999999 in
  let ok_cmp =
    fact 20 < fact 21 && - (fact 21) < - (fact 20) && fact 22 >= fact 22 &&
    pow2 64 > pow2 63 && not (pow2 64 <= pow2 63) && abs (- (pow2 70)) = pow2 70 &&
    FStar.Math.Lib.max (pow2 80) 3 = pow2 80 && FStar.Math.Lib.min (- (pow2 80)) 3 = - (pow2 80) in
  let ok_str =
    string_of_int (fact 25) = "15511210043330985984000000" &&
    string_of_int (- (pow2 70)) = "-1180591620717411303424" &&
    string_of_int 0 = "0" && string_of_int (-42) = "-42" in
  let ok_list =
    sum (range 0 100) = 4950 &&
    sum (range (pow2 62) 4) = 4 * pow2 62 + 6 in
  if not ok_fact then 1ul else if not ok_div then 2ul else
  if not ok_cmp then 3ul else if not ok_str then 4ul else
  if not ok_list then 5ul else 0ul

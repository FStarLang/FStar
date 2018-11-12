module Normalization
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val test : unit -> Lemma (FStar.List.Tot.length [1;2;3;1;2;3;1;2;3;1;2;3;1;2;3;1;2;3] == 18)
let test _ = assert_norm (FStar.List.Tot.length [1;2;3;1;2;3;1;2;3;1;2;3;1;2;3;1;2;3] == 18)

let rec id (x:nat) : Tot nat = match x with
  | 0 -> 0
  | i -> 1 + id (x - 1)

val test2 : unit -> Lemma (id 100 == 100)
let test2 _ = assert_norm (id 100 == 100)

val pow2_values: x:nat -> Lemma
  (requires True)
  (ensures (let p = pow2 x in
   match x with
   | 0  -> p=1
   | 1  -> p=2
   | 8  -> p=256
   | 16 -> p=65536
   | 31 -> p=2147483648
   | 32 -> p=4294967296
   | 63 -> p=9223372036854775808
   | 64 -> p=18446744073709551616
   | _  -> True))
  [SMTPat (pow2 x)]
let pow2_values x =
   match x with
   | 0  -> assert_norm (pow2 0 == 1)
   | 1  -> assert_norm (pow2 1 == 2)
   | 8  -> assert_norm (pow2 8 == 256)
   | 16 -> assert_norm (pow2 16 == 65536)
   | 31 -> assert_norm (pow2 31 == 2147483648)
   | 32 -> assert_norm (pow2 32 == 4294967296)
   | 63 -> assert_norm (pow2 63 == 9223372036854775808)
   | 64 -> assert_norm (pow2 64 == 18446744073709551616)
   | _  -> ()
let compare x y =
  if x < y then 1
  else if y < x then 0-1
  else 0
let test_sort = assert_norm (FStar.List.Tot.sortWith compare [10; 9; 8; 7; 6; 5; 4; 3; 2; 1] = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10])
let test_sort1 = assert_norm (FStar.List.Tot.sortWith (FStar.List.Tot.compare_of_bool (<)) [10; 9; 8; 7; 6; 5; 4; 3; 2; 1] = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10])


(*
 * Cf. #1529
 *)
[@"opaque_to_smt"]
let f_1529 (x:int) = 5

let f_1529_1 () =
  let f_local = normalize_term f_1529 in
  assert (f_local 2 == 5)

let f_1529_2 () =
  let f_local = norm [delta] f_1529 in
  assert (f_local 2 == 5)

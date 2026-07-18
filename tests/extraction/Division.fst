module Division

open FStar.All

(* This test checks that the OCaml runtime behavior of division and modulo
   coincide with what we can prove in F*, in particular as signs of the
   dividend and divisor vary. There is a similar test in karamel where
   the backend is C. *)

(* First a lemma to make sure %^ is actually remainder instead of modulo. *)
let sign (x : int) : int =
  if x < 0 then -1
  else if x > 0 then 1
  else 0

let rem_sign_matches_dividend (x y : Int32.t)
  : Lemma (requires (y <> 0l /\ Int32.fits (Int32.v x / Int32.v y)))
          (ensures ((x `Int32.rem` y = 0l) \/ (sign (Int32.v (x `Int32.rem` y)) = sign (Int32.v x))))
  = ()

let test_i8
  (x y : FStar.Int8.t{FStar.Int8.v y =!= 0 /\ FStar.Int8.fits (FStar.Int8.v x / FStar.Int8.v y)})
  (rdiv : FStar.Int8.t {rdiv == x `FStar.Int8.div` y})
  (rrem : FStar.Int8.t {rrem == x `FStar.Int8.rem` y})
  : ML unit =
  let open FStar.Int8 in
  if x `div` y <> rdiv || x `rem` y <> rrem then
    failwith "test_i8 failed"

let test_i16
  (x y : FStar.Int16.t{FStar.Int16.v y =!= 0 /\ FStar.Int16.fits (FStar.Int16.v x / FStar.Int16.v y)})
  (rdiv : FStar.Int16.t {rdiv == x `FStar.Int16.div` y})
  (rrem : FStar.Int16.t {rrem == x `FStar.Int16.rem` y})
  : ML unit =
  let open FStar.Int16 in
  if x `div` y <> rdiv || x `rem` y <> rrem then
    failwith "test_i16 failed"

let test_i32
  (x y : FStar.Int32.t{FStar.Int32.v y =!= 0 /\ FStar.Int32.fits (FStar.Int32.v x / FStar.Int32.v y)})
  (rdiv : FStar.Int32.t {rdiv == x `FStar.Int32.div` y})
  (rrem : FStar.Int32.t {rrem == x `FStar.Int32.rem` y})
  : ML unit =
  let open FStar.Int32 in
  if x `div` y <> rdiv || x `rem` y <> rrem then
    failwith "test_i32 failed"

let test_i64
  (x y : FStar.Int64.t{FStar.Int64.v y =!= 0 /\ FStar.Int64.fits (FStar.Int64.v x / FStar.Int64.v y)})
  (rdiv : FStar.Int64.t {rdiv == x `FStar.Int64.div` y})
  (rrem : FStar.Int64.t {rrem == x `FStar.Int64.rem` y})
  : ML unit =
  let open FStar.Int64 in
  if x `div` y <> rdiv || x `rem` y <> rrem then
    failwith "test_i64 failed"

let test_z
  (x y : int{y =!= 0})
  (rdiv : int {rdiv == x / y})
  (rrem : int {rrem == x % y})
  : ML unit =
  let open FStar.Int64 in
  if x / y <> rdiv || x % y <> rrem then
    failwith "test_i64 failed"

#set-options "--warn_error -272"

let _ : unit =
  test_i8 7y    2y    3y    1y;
  test_i8 7y    (-2y) (-3y) 1y;
  test_i8 (-7y) 2y    (-3y) (-1y);
  test_i8 (-7y) (-2y) 3y    (-1y)

let _ : unit =
  test_i16 7s    2s    3s    1s;
  test_i16 7s    (-2s) (-3s) 1s;
  test_i16 (-7s) 2s    (-3s) (-1s);
  test_i16 (-7s) (-2s) 3s    (-1s)

let _ : unit =
  test_i32 7l    2l    3l    1l;
  test_i32 7l    (-2l) (-3l) 1l;
  test_i32 (-7l) 2l    (-3l) (-1l);
  test_i32 (-7l) (-2l) 3l    (-1l)

let _ : unit =
  test_i64 7L    2L    3L    1L;
  test_i64 7L    (-2L) (-3L) 1L;
  test_i64 (-7L) 2L    (-3L) (-1L);
  test_i64 (-7L) (-2L) 3L    (-1L)

(* Unbounded integers use euclidean division, so the results are different. *)
let _ : unit =
  test_z 7    2    3    1;
  test_z 7    (-2) (-3) 1;
  test_z (-7) 2    (-4) 1;
  test_z (-7) (-2) 4    1

module Bug3426
open FStar.Real
let prim_arith_ty (p: unit): Type0 =
  let () = p in
  int -> int -> int

[@@expect_failure]
let prim_arith_sem (p: unit): (prim_arith_ty p) =
  fun x y -> x / y

[@@expect_failure]
let prim_arith_sem_mod (p: unit): (prim_arith_ty p) =
  fun x y -> x % y

let prim_arith_ty_real (p: unit): Type0 =
  let () = p in
  real -> real -> real

[@@expect_failure]
let prim_arith_sem_real (p: unit): (prim_arith_ty_real p) =
  fun x y -> x /. y
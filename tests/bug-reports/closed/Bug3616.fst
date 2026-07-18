module Bug3616

[@@"opaque_to_smt"]
let f (): int = 0

[@@expect_failure]
let _ =
  assert(f () == 0)

let _ =
  reveal_opaque (`%f) (f);
  assert(f () == 0)

[@@"opaque_to_smt"]
let rec f_rec (): int = 0

let _ =
  reveal_opaque (`%f_rec) (f_rec);
  assert(f_rec () == 0)

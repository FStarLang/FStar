module Bug4092

let is_zero (n: nat): bool =
  let rec maybe_zero (n: nat): Tot bool (decreases n) =
    if n = 0 then true
    else not_zero (n - 1)
  and not_zero (n: nat): Tot bool (decreases n) =
    if n = 0 then false
    else not_zero (n - 1)
  in maybe_zero n

let _ =
  assert_norm (is_zero 0 = true);
  assert_norm (is_zero 1 = false);
  ()

[@@expect_failure]
let _ = assert_norm (is_zero 0 = false)
[@@expect_failure]
let _ = assert_norm (is_zero 1 = true)

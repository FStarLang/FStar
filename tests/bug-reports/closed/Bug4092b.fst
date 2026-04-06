module Bug4092b

let is_even (n: nat): bool =
  let rec even (n: nat): Tot bool (decreases n) =
    if n = 0 then true
    else odd (n - 1)
  and odd (n: nat): Tot bool (decreases n) =
    if n = 0 then false
    else even (n - 1)
  in even n

let _ =
  assert_norm (is_even 0 = true);
  assert_norm (is_even 1 = false);
  assert_norm (is_even 2 = true);
  assert_norm (is_even 3 = false);
  ()

module Bug3120b

(* This _will_ fail, but it should fail gracefully instead of exploding. *)
[@@expect_failure [66]]
effect {
  IOw (a : Type u#asd)
  with {
    repr         = magic();
    return       = magic();
    bind         = magic();
    subcomp      = magic();
    if_then_else = magic();
  }
}

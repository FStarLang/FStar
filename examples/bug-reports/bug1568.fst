module Bug1568

[@(expect_failure [189])]
noeq type t a =
  | T: t

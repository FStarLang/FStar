module Bug1488

assume val phi :Type0

[@expect_failure [185]]
type test =
  | Test : unit -> t:test{phi}

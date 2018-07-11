module PatCoerce

assume val test: u:unit -> Type0

val bla: unit -> nat

[@ (expect_failure [189])]
let bla u =
  match test u with
  | true -> 0
  | false -> 1

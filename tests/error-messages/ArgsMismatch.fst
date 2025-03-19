module ArgsMismatch

(* Attributes on arguments don't matter at all for applications. *)

let foo (#x:int) (y:int) = x+y

[@@expect_failure] let _ = foo 1 2
[@@expect_failure] let _ = foo #1 #2
                   let _ = foo #1 2
[@@expect_failure] let _ = foo 1 #2

let bar (#[@@@1]x:int) (y:int) = x+y

[@@expect_failure] let _ = bar 1 2
[@@expect_failure] let _ = bar #1 #2
                   let _ = bar #1 2
[@@expect_failure] let _ = bar 1 #2

let baz (#x:int) ([@@@2]y:int) = x+y

[@@expect_failure] let _ = baz 1 2
[@@expect_failure] let _ = baz #1 #2
                   let _ = baz #1 2
[@@expect_failure] let _ = baz 1 #2

let qux (#[@@@1]x:int) ([@@@2]y:int) = x+y

[@@expect_failure] let _ = qux 1 2
[@@expect_failure] let _ = qux #1 #2
                   let _ = qux #1 2
[@@expect_failure] let _ = qux 1 #2

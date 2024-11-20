module DesugarOrder

(* Report 'a' as not found, instead of 'c'. It's clearer
to report errors in textual order. Ideally, we could report all of them
at once (also in order). *)
[@@expect_failure]
let _ = (+) a b c

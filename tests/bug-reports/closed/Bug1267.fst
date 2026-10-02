module Bug1267

// Nested ordinary comments must not terminate an enclosing documentation comment.
(** A (* B *) **)
let a = 1

(** Outer (* middle (* inner *) middle *) outer **)
let b = 2

let _ = assert_norm (a + b == 3)

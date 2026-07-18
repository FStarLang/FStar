module RecordUpdate

(* This should work, even if `t` is not declared as a record.*)
type t = | T : int -> t
let f (x:t) = {x with _0 = 1}

(* These should also work with type annotations and pattern matching *)
let g (x:t) : t = {x with _0 = 1}
let h () : t = { _0 = 1 }
let i (x:t) = match x with | { _0 = n } -> n

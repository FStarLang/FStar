module RecordUpdate

(* This should work, even if `t` is not declared as a record.*)
type t = | T : int -> t
let f (x:t) = {x with _0 = 1}

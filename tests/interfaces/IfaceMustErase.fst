module IfaceMustErase

(* `unit` is erased during extraction, but `val t1 : Type0` hides that from
   clients: warning 318. *)
let t1 = unit

(* Conversely, `bool` is informative, so the `erasable` attribute that
   `val t3` puts on this definition cannot be honoured: error 162. *)
let t3 = bool

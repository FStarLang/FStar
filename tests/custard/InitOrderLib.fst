module InitOrderLib

open FStar.All

let r : ref int = alloc 0

(* An initializer: nothing refers to it. *)
let _ = r := 42

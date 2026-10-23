module CherryPap
module U32 = FStar.UInt32
open FStar.All

(* A partial application builds a closure and runs nothing, so it is not
   followed by an exception test even though the function raises
   (cherry.md, "Integers, strings, exceptions"). *)
let check (k: int) (x: int) : ML int =
  if x < 0 then failwith "negative" else x + k

let make (k: int) : ML (list (int -> ML int)) = [check k; check (k + 1)]

let main () : ML U32.t =
  match make 3 with
  | [f; g] ->
    let ok = f 4 = 7 && g 4 = 8 in
    let raised = try let _ = g (-1) in false with _ -> true in
    if ok && raised then 0ul else 1ul
  | _ -> 1ul

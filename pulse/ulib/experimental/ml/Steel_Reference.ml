type 'a ref = 'a Steel_HigherReference.ref

(*
 * TODO: What about null and is_null?
 *)

let alloc = Steel_HigherReference.alloc
let read = Steel_HigherReference.read
let read_refine = Steel_HigherReference.read_refine
let write = Steel_HigherReference.write
let free = Steel_HigherReference.free

let cas (uses:unit) (r:'a ref) (v:unit) (v_old:'a) (v_new:'a) =
  Steel_Common.Steel_function_unsupported "cas"


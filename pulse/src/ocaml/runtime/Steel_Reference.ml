type 'a ref = 'a Steel_HigherReference.ref

(*
 * TODO: What about null and is_null?
 *)

let alloc_pt = Steel_HigherReference.alloc
let read_pt = Steel_HigherReference.read
let read_refine_pt = Steel_HigherReference.read_refine
let write_pt = Steel_HigherReference.write
let free_pt = Steel_HigherReference.free

let cas_pt (uses:unit) (r:'a ref) (v:unit) (v_old:'a) (v_new:'a) =
  Steel_Common.Steel_function_unsupported "cas"


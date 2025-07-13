let op_Bang (r:'a ref) () () = !r
let read = op_Bang
let op_Colon_Equals (r:'a ref) (v:'a) () = r := v
let write = op_Colon_Equals
let alloc (v:'a) = ref v

(* dummy null ref *)
let __null : int ref = alloc 0

let null : 'a. unit -> 'a ref =
  fun () -> Obj.magic __null

let is_null : 'a. 'a ref -> bool =
  fun r -> r == Obj.magic __null

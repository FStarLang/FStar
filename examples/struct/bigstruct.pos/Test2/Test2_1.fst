module Test2_1

module DM = FStar.DependentMap
module S  = FStar.Pointer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

type struct_fd =
| F1

let struct_struct_ty = function
| F1 -> int

let struct_struct = DM.t struct_fd struct_struct_ty

let struct = S.pointer struct_struct

let write_struct_spec () : Tot struct_struct =
  DM.create #_ #struct_struct_ty (function
  | F1 -> 1
)

let write_struct (s : struct) : HST.Stack unit
  (requires (fun h -> Pointer.live h s))
  (ensures (fun h0 _ h1 ->
    Pointer.live h1 s /\
    (Pointer.gread h1 s) == (write_struct_spec ())
  ))
=
  let _ = Pointer.write (Pointer.field s F1) 1 in
  let h1 = HST.get () in
  assert (DM.equal (Pointer.gread h1 s) (write_struct_spec ()))



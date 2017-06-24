module Test1_1

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

let write_struct_spec (h : HS.mem) (s : struct) : GTot Type0 =
  Pointer.gread h (Pointer.gfield s F1) = 1 /\
  True

let write_struct (s : struct) : HST.Stack unit
  (requires (fun h -> Pointer.live h s))
  (ensures (fun h0 _ h1 ->
    Pointer.live h1 s /\
    write_struct_spec h1 s
  ))
=
  let _ = Pointer.write (Pointer.field s F1) 1 in
  ()



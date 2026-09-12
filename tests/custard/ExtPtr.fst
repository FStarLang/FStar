module ExtPtr
module U8 = FStar.UInt8
module I32 = FStar.Int32
open FStar.All
open FStar.Attributes

[@@custard_extern "extptr_base"; custard_c_header "ExtPtr_stubs.h"]
assume val base (off : FStar.SizeT.t) : ML (ref U8.t)

let main () : ML I32.t =
  let p = base 0sz in
  if U8.eq !p 7uy then 0l else 1l

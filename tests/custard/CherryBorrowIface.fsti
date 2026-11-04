module CherryBorrowIface
open FStar.All
module U32 = FStar.UInt32

val head_or (#a:Type) (r: ref (list a)) (d: a) : ML a
val main : unit -> ML U32.t

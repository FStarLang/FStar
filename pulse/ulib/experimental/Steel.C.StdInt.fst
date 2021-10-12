module Steel.C.StdInt
include Steel.C.StdInt.Base

open Steel.C.Fields
open Steel.C.Typedef
open Steel.C.Opt

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

[@@c_typedef]
noextract inline_for_extraction
let size: typedef = opt_typedef size_t

[@@c_typedef]
noextract inline_for_extraction
let uint16: typedef = opt_typedef U16.t

[@@c_typedef]
noextract inline_for_extraction
let uint32: typedef = opt_typedef U32.t

[@@c_typedef]
noextract inline_for_extraction
let uint64: typedef = opt_typedef U64.t

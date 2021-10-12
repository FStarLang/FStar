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
let size: typedef = {
  carrier = option size_t;
  pcm = opt_pcm #size_t;
  view_type = size_t;
  view = opt_view size_t;
  is_unit = (fun x -> None? x);
}

[@@c_typedef]
noextract inline_for_extraction
let uint16: typedef = {
  carrier = option U16.t;
  pcm = opt_pcm #U16.t;
  view_type = U16.t;
  view = opt_view U16.t;
  is_unit = (fun x -> None? x);
}


[@@c_typedef]
noextract inline_for_extraction
let uint32: typedef = {
  carrier = option U32.t;
  pcm = opt_pcm #U32.t;
  view_type = U32.t;
  view = opt_view U32.t;
  is_unit = (fun x -> None? x);
}

[@@c_typedef]
noextract inline_for_extraction
let uint64: typedef = {
  carrier = option U64.t;
  pcm = opt_pcm #U64.t;
  view_type = U64.t;
  view = opt_view U64.t;
  is_unit = (fun x -> None? x);
}


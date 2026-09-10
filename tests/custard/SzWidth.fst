(* Section 95.  What --custard_sizet_width has to reach: the type of a
   binder, a literal and its suffix, both directions of the FStar.SizeT
   conversions (which are casts, so they print their target through the same
   function), a struct field, and the length of a local array -- whose loop
   counter is a size_t whatever the length's width is. *)
module SzWidth
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module U64 = FStar.UInt64

(* The assumption that licenses --custard_sizet_width 32 in the first place.
   Custard does not read it -- it cannot, it is an [assume] about a refinement
   -- but a program that does not have it cannot use the flag soundly, so the
   test states it where a reader of the test will see it. *)
assume SizeTFitsU32 : SZ.fits_u32

type box = { len : (n:SZ.t{SZ.v n < 65000}); tag : U32.t }

(* Not a literal: a [size_t] literal is checked against [fits] statically and
   4294967295 is past it.  The conversion has [fits_u32] as its precondition,
   which is what the assumption above is for. *)
let big : SZ.t = SZ.uint32_to_sizet 4294967295ul

let widen (n : SZ.t) : U64.t = SZ.sizet_to_uint64 n

let narrow (n : SZ.t) : U32.t = SZ.sizet_to_uint32 n

let of_u32 (n : U32.t) : SZ.t = SZ.uint32_to_sizet n

let stride (b : box) : SZ.t = SZ.add b.len 1sz

let main () : FStar.All.ML Int32.t =
  let b = { len = of_u32 7ul; tag = 3ul } in
  let s = stride b in
  if SZ.eq s 8sz && U64.eq (widen s) 8UL && U32.eq (narrow big) 4294967295ul
  then 0l else 1l

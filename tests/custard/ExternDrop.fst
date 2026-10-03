module ExternDrop
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All
open FStar.Attributes

(* Section 5.1 and section 74, on an external's declaration.

   [split_mono_args] deletes a [Dropped] argument outright -- it is not even
   passed as [()] -- so a declaration that keeps the binder is one parameter
   longer than every call to it, and the C compiler is what finds out.

   [major]'s spine is the second half: the codomain is an abbreviation, and
   splitting the declared type without unfolding it stops one binder early,
   which puts the erased [unit] on the declaration's side and not on the
   call's.  The two halves are one test because the shape EverParse has --
   [val cbor_det_major_type () : get_major_type_t _] -- is both at once.

   Compiling is the assertion.  A disagreement here is a call with the wrong
   number of arguments, which no C compiler accepts. *)

type scale_t = U32.t -> U32.t

[@@custard_extern "ed_major"; custard_c_header "ExternDrop_stubs.h"]
assume val major (_:unit) : scale_t

[@@custard_extern "ed_scale"; custard_c_header "ExternDrop_stubs.h"]
assume val scale (_:unit) (n:U32.t) : U32.t

let main () : I32.t =
  if U32.eq (major () 1ul) 2ul && U32.eq (scale () 3ul) 6ul then 0l else 1l

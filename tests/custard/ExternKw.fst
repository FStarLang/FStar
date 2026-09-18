module ExternKw

open FStar.All

module U64 = FStar.UInt64
module U32 = FStar.UInt32

(* Section 45.1.  A [@@custard_extern] target is a symbol that already exists
   on the other side, spelled the way its own language spells it -- so it is
   emitted verbatim, and that includes a C keyword.

   The keyword case is not hypothetical: the operand of a C++ template
   argument list or of a type-taking macro is often exactly a keyword.
   Kuiper's Tensor Core accumulator is [wmma::fragment<..., float>], and
   there is no other way to write [float].  Escaping it to [float_] could
   not have caught a mistake -- it turns a link error against a name the
   program wrote into one against a name it did not.

   The external *type* path has always been verbatim, which is what lets
   Kuiper spell a fragment's type as [auto]; this pins that the value path
   agrees. *)

assume new type tok : Type0

[@@FStar.Attributes.custard_extern "float";
   FStar.Attributes.custard_c_header "ExternKw_stubs.h"]
assume val kw_float : tok

[@@FStar.Attributes.custard_extern "KW_SIZEOF";
   FStar.Attributes.custard_c_header "ExternKw_stubs.h"]
assume val kw_sizeof : tok -> U64.t

let main () : ML U32.t =
  if kw_sizeof kw_float = 4uL then 0ul else 1ul

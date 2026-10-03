module NarrowOverride

open FStar.All

module U16 = FStar.UInt16
module U32 = FStar.UInt32

(* Section 66.  The narrow-float support block is overridable, and the
   override arrives through [@@custard_c_header] -- which only works if those
   includes are emitted above the block.  Kuiper is the motivating consumer:
   [wmma::fragment] is a template over CUDA's [__half], so a fragment holding
   Custard's two-byte struct is not a type any [wmma] overload accepts, and
   the way out is to make [custard_f16] be [__half] before the block is
   reached.  There is no earlier place to say so: the header is named by an
   attribute on an F* declaration.

   [NarrowOverride_stubs.h] defines CUSTARD_FLOAT16_DEFINED and its own
   [custard_f16].  If the block were emitted first, this file would be a
   redefinition and the translation unit would not compile, so the ordering
   is checked by the C compiler rather than by a grep. *)

[@@FStar.Attributes.custard_float 16]
assume val t : Type0

assume val add : t -> t -> t
assume val ieee_eq : t -> t -> bool
assume val of_int : Int64.t -> t
assume val of_literal : string -> t
assume val zero : t
assume val one : t

(* The declaration that names the header.  It also reads the override's own
   member, so the test fails if some other [custard_f16] were in scope. *)
[@@FStar.Attributes.custard_extern "narrow_override_bits";
   FStar.Attributes.custard_c_header "NarrowOverride_stubs.h"]
assume val bits : t -> U16.t

let main () : ML U32.t =
  (* 1.5 at binary16 is 0x3E00 = 15872, and Custard emits that bit pattern
     through the override's CUSTARD_F16_LIT. *)
  let ok1 = bits (of_literal "1.5") = 15872us in
  let ok2 = ieee_eq (add (of_int 1L) (of_int 2L)) (of_literal "3.0") in
  let ok3 = ieee_eq (add zero one) one in
  if ok1 && ok2 && ok3 then 0ul else 1ul

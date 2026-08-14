module Spec.Hash.Definitions

module US = FStar.SizeT

(* Custard: the type is a C enum declared by EverCrypt's own headers, so it
   has no F* definition to compile.  The karamel backend spells it
   [Spec_Hash_Definitions_hash_alg] on its own; the direct-to-C backend needs
   the name written out. *)
[@@FStar.Attributes.custard_extern "Spec_Hash_Definitions_hash_alg";
  FStar.Attributes.custard_c_header "EverCrypt_Base.h"]
val hash_alg :  _ : Type0 { US.fits_u32 }
val sha2_256 : hash_alg

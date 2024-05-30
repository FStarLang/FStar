module Spec.Hash.Definitions

module US = FStar.SizeT

val hash_alg :  _ : Type0 { US.fits_u32 }
val sha2_256 : hash_alg

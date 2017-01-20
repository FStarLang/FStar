module HyE.PlainHPKE

open HyE.Flags
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Monotonic.RRef
open Platform.Bytes


abstract type protected_hpke_plain = bytes 
assume Plain_hasEq: hasEq protected_hpke_plain
type hpke_plain = bytes

(* two pure functions, never called when ideal *)
val repr: p:protected_hpke_plain{not hpke_ind_cca} -> Tot hpke_plain
let repr p = p       (* a pure function from t to RSA.plain *)

// Change this if we want to use signcryption with hpke_int-ctxt
val coerce: x:hpke_plain -> Tot protected_hpke_plain
let coerce x = x  

val length: protected_hpke_plain -> Tot nat
let length p = length p

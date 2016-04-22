module Bignum.Parameters

open FStar.Ghost
open IntLib

let op_Star = Prims.op_Multiply

val prime: erased pos
let prime = admit()
val platform_size: pos // Maybe should be removed
let platform_size = 64
val platform_wide: w:pos{w = 2 * platform_size }
let platform_wide = 128
val norm_length: pos
let norm_length = 5
val bytes_length: pos
let bytes_length = 32
val templ: nat -> Tot pos
let templ = fun n -> 51
val a24: string
let a24 = "121665"
val a24':nat
let a24' = 121665
val ndiff: n:pos{n <= platform_size /\ (forall (i:nat). {:pattern (templ i)} i < norm_length ==> templ i < n)}
let ndiff = 53
val ndiff': n:pos{n < ndiff /\ (forall (i:nat). i < norm_length ==> templ i <= n)}
let ndiff' = 51

(* Required at least for addition *)
val parameters_lemma_0:
  unit -> Lemma (requires (True)) 
	        (ensures (forall (i:nat). {:pattern (templ i)} i < 2*norm_length - 1 ==> templ i < platform_size - 1))
let parameters_lemma_0 () = ()

val parameters_lemma_1:
  unit -> Lemma (requires (True))
	        (ensures (platform_wide - 1 >= log_2 norm_length))
let parameters_lemma_1 () = ()

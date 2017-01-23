module Curve.Parameters

open Math.Lib
open FStar.Mul
open FStar.Ghost

val prime: erased pos
let prime =
  assert_norm (0 < pow2 255 - 19);
  hide (pow2 255 - 19)
let platform_size: pos = 64
let platform_wide: pos = 128
let norm_length: pos = 5
let nlength: x:UInt32.t{UInt32.v x = 5} = 5ul
let bytes_length: pos = 32
let blength: x:UInt32.t{UInt32.v x = 32} = assert_norm (32 < pow2 32); 32ul
let templ: (nat -> Tot pos) = fun i -> 51
let a24' = 121665
let a24 = assert_norm (121665 < pow2 64); 121665uL

(* Required at least for addition *)
val parameters_lemma_0: unit -> Lemma
  (forall (i:nat). i < 2*norm_length - 1 ==> templ i < platform_size)
let parameters_lemma_0 () = ()

val parameters_lemma_1: unit -> Lemma
  (platform_wide - 1 >= log_2 norm_length)
let parameters_lemma_1 () = ()

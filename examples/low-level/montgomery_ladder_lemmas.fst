(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Parameters --verify_module MontgomeryLadderLemmas;
    variables:MATH=../math_interfaces BIGNUM=../bignum_proof;
    other-files:FStar.Ghost.fst $BIGNUM/axiomatic.fst $BIGNUM/intlib.fst $BIGNUM/lemmas.fst $BIGNUM/parameters.fsti $BIGNUM/uint.fst 
  --*)

module MontgomeryLadderLemmas

open FStar.Ghost
open IntLib
open UInt
open Parameters

val lemma_0: x:nat -> y:nat -> Lemma (requires (x<=y /\ x - y <> 0)) (ensures (x<y))
let lemma_0 x y = ()
val lemma_1: x:int -> y:int -> Lemma (requires (x - y <> 0)) (ensures (x <> y))
let lemma_1 x y = ()
val lemma_2: x:int -> y:int -> Lemma (requires (x <= y /\ x <> y)) (ensures (x < y))
let lemma_2 x y = ()	
val lemma_3: norm_length:nat -> ctr:nat ->
  Lemma (requires (ctr <= norm_length /\ norm_length - ctr <> 0)) (ensures (ctr < norm_length))
let lemma_3 norm_length ctr = lemma_1 norm_length ctr; lemma_2 ctr norm_length

val lemma_4: n:nat -> m:nat -> Lemma (requires (True)) (ensures (n * pow2 8 + m >= 0)) //[SMTPat (n * pow2 8 + m)]
let lemma_4 n m = 
  Axiomatic.nat_times_nat_is_nat n (pow2 8)

assume val lemma_5:
  a:erased nat -> b:byte -> n:nat{ n < 8 } ->
  Lemma
    (requires (True))
    (ensures (let a = reveal a in 2 * (a * (pow2 n) + (v b / (pow2 (8-n)))) + ((v b / (pow2 (7-n))) % 2) = 
                                 a * (pow2 (n+1)) + v b / (pow2 (8-(n+1)))))

assume val lemma_6:
  n:nat -> m:nat ->
  Lemma
    (requires ( m >= 0 /\ bitsize m 8 ))
    (ensures ( n * (pow2 0) + (m / (pow2 8)) = n ))

assume val lemma_71: n:nat -> m:nat -> Lemma (requires (True)) (ensures (n * m >= 0))
//let lemma_71 n m = ()

val lemma_7: scalar:nat -> byte:byte -> 
  Lemma (requires (True))
	(ensures (scalar * pow2 8 + v byte >= 0))
	[SMTPat (scalar * pow2 8 + v byte)]
let lemma_7 s b = 
  lemma_71 s (pow2 8)

assume val and_one_lemma:
  b:byte -> Lemma (log_and_byte b one_byte == zero_byte \/ log_and_byte b one_byte = one_byte)

val positive_byte: b:byte -> Lemma (v b >= 0)
let positive_byte b = ()

val formula_0: scalar:erased nat -> byte:byte -> GTot (erased nat)
let formula_0 scalar byte = 
  lemma_7 (reveal scalar) byte;
  hide (reveal scalar * pow2 8 + v byte)

val formula_1: n:FStar.Ghost.erased nat -> b:UInt.byte -> GTot (z:erased nat{reveal z = 2*FStar.Ghost.reveal n+v b})
let formula_1 n b = 
  lemma_71 2 (FStar.Ghost.reveal n);
  positive_byte b;
  hide (2*FStar.Ghost.reveal n+v b)

opaque val ghelper_lemma_1:
  n:erased nat -> m:byte ->
  GLemma unit
    (requires (True))
    (ensures (reveal n * (pow2 8) + (v m / (pow2 (8-8))) = reveal (formula_0 n m))) []
let ghelper_lemma_1 n m =
  admit();
  cut(True /\ pow2 (8-8) = 1); 
  Axiomatic.slash_star_axiom (v m) 1 (v m)

val helper_lemma_1:
  n:erased nat -> m:byte ->
  Lemma 
    (requires (True))
    (ensures (reveal n * (pow2 8) + (v m / (pow2 (8-8))) = reveal (formula_0 n m))) 
let helper_lemma_1 n m = 
  coerce
    (requires (True))
    (ensures (reveal n * (pow2 8) + (v m / (pow2 (8-8))) = reveal (formula_0 n m))) 
    (fun _ -> ghelper_lemma_1 n m)

assume val formula_2: n:nat -> b:UInt.byte -> Tot (z:FStar.Ghost.erased nat{FStar.Ghost.reveal z = 2*n+v b})
assume val eformula_2: n:erased nat -> b:UInt.byte -> Tot (z:FStar.Ghost.erased nat{FStar.Ghost.reveal z = 2*reveal n+v b})

val formula_lemma: n:erased nat -> b:UInt.byte -> Lemma (eformula_2 n b = formula_1 n b)
let formula_lemma n b = ()
(*
let formula_2 n b = 
  lemma_71 2 n;
  positive_byte b;
  FStar.Ghost.hide (2*n+v b)
*)

assume val lemma_8: n:nat -> Lemma (requires (True)) (ensures (n + n = 2 * n + 0 /\ n + (n+1) = (2*n+0) + 1 /\ (n+1) + n = 2 * n + 1 /\ (n+1) + (n+1) = (2*n+1)+1))
//let lemma_8 n = ()

val lemma_9: ctr:nat -> Lemma (requires (8-ctr=0)) (ensures (ctr = 8))
let lemma_9 ctr = ()

val lemma_101: s:nat -> ctr:nat -> 
  Lemma (requires (ctr < 8))
	(ensures (8 - (ctr+1) >= 0 /\ pow2 (8 - (ctr+1)) > 0))
let lemma_101 s ctr = ()	

val glemma_10: s:erased nat -> ctr:nat -> b:byte ->
  GLemma unit
	 (requires (ctr < 8))
	 (ensures (v b >= 0 
	  /\ 8-(ctr+1) >= 0
	  /\ pow2 (8-(ctr+1)) > 0 /\ reveal s * (pow2 (ctr+1)) + (v b / pow2 (8 - (ctr+1))) >= 0))
	  []
let glemma_10 s ctr b = 
  cut (True /\ 8 - (ctr+1) >= 0); 
  positive_byte b;
  Axiomatic.nat_times_nat_is_nat (reveal s) (pow2 (ctr+1));
  Axiomatic.nat_over_pos_is_nat (v b) (pow2 (8-(ctr+1)));
  lemma_101 (reveal s) ctr

val lemma_10: s:erased nat -> ctr:nat -> b:byte ->
  Lemma
	 (requires (ctr < 8))
	 (ensures (v b >= 0 
	  /\ 8-(ctr+1) >= 0
	  /\ pow2 (8-(ctr+1)) > 0 /\ reveal s * (pow2 (ctr+1)) + (v b / pow2 (8 - (ctr+1))) >= 0))
let lemma_10 s ctr b =
  coerce
  	 (requires (ctr < 8))
	 (ensures (v b >= 0 
	  /\ 8-(ctr+1) >= 0
	  /\ pow2 (8-(ctr+1)) > 0 /\ reveal s * (pow2 (ctr+1)) + (v b / pow2 (8 - (ctr+1))) >= 0))
	  (fun _ -> glemma_10 s ctr b)

val div_nat_lemma: n:nat -> d:pos -> Lemma (n/d >= 0)
let div_nat_lemma n d = ()

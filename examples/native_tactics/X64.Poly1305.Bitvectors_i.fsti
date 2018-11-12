module X64.Poly1305.Bitvectors_i

open FStar.BV
open FStar.Mul
open FStar.UInt

val lemma_shr2: (x:uint_t 64) -> Lemma
  ((shift_right #64 x 2 == udiv #64 x 4))
  [SMTPat (shift_right #64 x 2)]
val lemma_shr4: x:uint_t 64 -> Lemma (shift_right #64 x 4 == udiv #64 x 16)
				    [SMTPat (shift_right #64 x 4)]
val lemma_and_mod_n: x:uint_t 64 -> Lemma (logand #64 x 3 == mod #64 x 4 /\ 
					 logand #64 x 15 == mod #64 x 16)
				   [SMTPat (logand #64 x 3); 
				    SMTPat (logand #64 x 15)]
				    
val lemma_clear_lower_2: x:uint_t 8 -> 
  Lemma (logand #8 x 0xfc == mul_mod #8 (udiv #8 x 4) 4)
  [SMTPat (logand #8 x 0xfc)]
val lemma_and_constants: x:uint_t 64 ->
  Lemma (logand #64 x 0 == 0 /\ logand #64 x 0xffffffffffffffff == x)
  [SMTPat (logand #64 x 0); SMTPat (logand #64 x 0xffffffffffffffff)]
val lemma_poly_constants: x:uint_t 64 -> 
  Lemma (logand #64 x 0x0ffffffc0fffffff < 0x1000000000000000 /\
	 logand #64 x 0x0ffffffc0ffffffc < 0x1000000000000000 /\
	 mod #64 (logand #64 x 0x0ffffffc0ffffffc) 4 == 0)
  [SMTPat (logand #64 x 0x0ffffffc0fffffff);
   SMTPat (logand #64 x 0x0ffffffc0ffffffc);
   SMTPat (logand #64 x 0x0ffffffc0ffffffc)]
val lemma_and_commutes: x:uint_t 64 -> y:uint_t 64 ->
  Lemma (logand #64 x y == logand #64 y x)
val lemma_bv128_64_64_and_helper: x:bv_t 128 -> x0:bv_t 64 -> x1:bv_t 64 ->
  y:bv_t 128 -> y0:bv_t 64 -> y1:bv_t 64 ->
  z:bv_t 128 -> z0:bv_t 64 -> z1:bv_t 64 ->
  Lemma (requires (z0 == bvand #64 x0 y0 /\
		   z1 == bvand #64 x1 y1 /\
		   x == bvor #128 (bvshl #128 (bv_uext #64 #64 x1) 64) 
							   (bv_uext #64 #64 x0) /\
		   y == bvor #128 (bvshl #128 (bv_uext #64 #64 y1) 64) 
							   (bv_uext #64 #64 y0) /\
		   z == bvor #128 (bvshl #128 (bv_uext #64 #64 z1) 64) 
							   (bv_uext #64 #64 z0)))
	(ensures (z == bvand #128 x y))
val bv128_64_64: x1:bv_t 64 -> x0:bv_t 64 -> Tot (bv_t 128)

val lemma_bv128_64_64_and: x:bv_t 128 -> x0:bv_t 64 -> x1:bv_t 64 ->
  y:bv_t 128 -> y0:bv_t 64 -> y1:bv_t 64 ->
  z:bv_t 128 -> z0:bv_t 64 -> z1:bv_t 64 ->
  Lemma (requires (z0 == bvand #64 x0 y0 /\
		   z1 == bvand #64 x1 y1 /\
		   x == bv128_64_64 x1 x0 /\
		   y == bv128_64_64 y1 y0 /\
		   z == bv128_64_64 z1 z0))
	(ensures (z == bvand #128 x y))

val lemma_bytes_shift_constants0: unit -> Lemma
    (shift_left #64 0 3 == 0 /\
	     shift_left #64 1 (shift_left #64 0 3) == 0x1)

val lemma_bytes_shift_constants1: unit -> Lemma
    (shift_left #64 1 3 == 8 /\
	     shift_left #64 1 (shift_left #64 1 3) == 0x100)

val lemma_bytes_shift_constants2: unit -> Lemma
    (shift_left #64 2 3 == 16 /\
	     shift_left #64 1 (shift_left #64 2 3) == 0x10000)

val lemma_bytes_shift_constants3: unit -> Lemma
    (shift_left #64 3 3 == 24 /\
	     shift_left #64 1 (shift_left #64 3 3) == 0x1000000)

val lemma_bytes_shift_constants4: unit -> Lemma
    (shift_left #64 4 3 == 32 /\
	     shift_left #64 1 (shift_left #64 4 3) == 0x100000000)

val lemma_bytes_shift_constants5: unit -> Lemma
    (shift_left #64 5 3 == 40 /\
	     shift_left #64 1 (shift_left #64 5 3) == 0x10000000000)

val lemma_bytes_shift_constants6: unit -> Lemma
    (shift_left #64 6 3 == 48 /\
	     shift_left #64 1 (shift_left #64 6 3) == 0x1000000000000)

val lemma_bytes_shift_constants7: unit -> Lemma
    (shift_left #64 7 3 == 56 /\
	     shift_left #64 1 (shift_left #64 7 3) == 0x100000000000000)

val lemma_bytes_and_mod0: x: uint_t 64 ->
  Lemma (logand #64 x  (0x1 - 1) == mod #64 x 0x1)
val lemma_bytes_and_mod1: x: uint_t 64 ->
  Lemma (logand #64 x  (0x100 - 1) == mod #64 x 0x100)
val lemma_bytes_and_mod2: x: uint_t 64 ->
  Lemma (logand #64 x  (0x10000 - 1) == mod #64 x 0x10000)
val lemma_bytes_and_mod3: x: uint_t 64 ->
  Lemma (logand #64 x  (0x1000000 - 1) == mod #64 x 0x1000000)
val lemma_bytes_and_mod4: x: uint_t 64 ->
  Lemma (logand #64 x  (0x100000000 - 1) == mod #64 x 0x100000000)
val lemma_bytes_and_mod5: x: uint_t 64 ->
  Lemma (logand #64 x  (0x10000000000 - 1) == mod #64 x 0x10000000000)
val lemma_bytes_and_mod6: x: uint_t 64 ->
  Lemma (logand #64 x  (0x1000000000000 - 1) == mod #64 x 0x1000000000000)
val lemma_bytes_and_mod7: x: uint_t 64 ->
  Lemma (logand #64 x  (0x100000000000000 - 1) == mod #64 x 0x100000000000000)

val lemma_bytes_and_mod: x: uint_t 64 -> y:uint_t 64 ->
  Lemma (requires (y < 8))
	(ensures (shift_left #64 y 3 < 64 /\ 
		   (shift_left #64 1 (shift_left #64 y 3)) <> 0 /\ 
		   logand #64 x (((shift_left #64 1 (shift_left #64 y 3))) - 1) == 
		     mod #64 x (shift_left #64 1 (shift_left #64 y 3))))

val lemma_bytes_power2: unit ->
Lemma (ensures (pow2 0 == 0x1 /\
	        pow2 8 == 0x100 /\
		pow2 16 == 0x10000 /\
		pow2 24 == 0x1000000 /\
		pow2 32 == 0x100000000 /\
		pow2 40 == 0x10000000000 /\
		pow2 48 == 0x1000000000000 /\
		pow2 56 == 0x100000000000000))

val lemma_bytes_shift_power2: y:uint_t 64 ->
  Lemma (requires (y < 8))
	(ensures  (shift_left #64 y 3 < 64 /\
		   y * 8 == shift_left #64 y 3 /\
		   pow2 (shift_left #64 y 3) == shift_left #64 1 (shift_left #64 y 3)))

module FStar.BV

val bv_t: (n : nat) -> Type0

(* Redefining basic type from UInt to avoid importing UInt *)
(* Reduces verification time by 50% in small examples *)
let max_int (n:nat) : Tot int = pow2 n - 1
let min_int (n:nat) : Tot int = 0
let fits (x:int) (n:nat) : Tot bool = min_int n <= x && x <= max_int n
let size (x:int) (n:nat) : Tot Type0 = b2t(fits x n)
type uint_t' (n:nat) = x:int{size x n}

val logand_vec: #n:pos -> a:bv_t n -> b:bv_t n -> Tot (bv_t n)

val logxor_vec: #n:pos -> a:bv_t n -> b:bv_t n -> Tot (bv_t n)

val logor_vec: #n:pos -> a:bv_t n -> b:bv_t n -> Tot (bv_t n)

val lognot_vec: #n:pos -> a:bv_t n -> Tot (bv_t n)

val shift_left_vec: #n:pos -> a:bv_t n -> s:nat -> Tot (bv_t n)

val shift_right_vec: #n:pos -> a:bv_t n -> s:nat -> Tot (bv_t n)

val to_vec: #n:nat -> num:uint_t' n -> Tot (bv_t n)

val from_vec: #n:nat -> vec:bv_t n -> Tot (uint_t' n)

let zero_vec #n = to_vec #n 0

val to_vec_lemma_1: #n:nat -> a:uint_t' n -> b:uint_t' n ->
  Lemma (requires a = b) (ensures (to_vec #n a = to_vec #n b))

val to_vec_lemma_2: #n:nat -> a:uint_t' n -> b:uint_t' n ->
  Lemma (requires (to_vec a = to_vec b)) (ensures a = b)

val div_vec :#n:pos -> a:bv_t n -> b:bv_t n{from_vec #n b <> 0} -> Tot (bv_t n)
  
val mod_vec :#n:nat -> a:bv_t n -> b:bv_t n{from_vec #n b <> 0} -> Tot (bv_t n)

val inverse_vec_lemma: #n:nat -> vec:bv_t n ->
  Lemma (requires True) (ensures vec = (to_vec (from_vec vec)))
        [SMTPat (to_vec (from_vec vec))]

val inverse_num_lemma: #n:nat -> num:uint_t' n ->
  Lemma (requires True) (ensures num = from_vec #n (to_vec #n num))
        [SMTPat (from_vec #n (to_vec #n num))]

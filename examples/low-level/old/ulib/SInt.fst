module SInt
open Axioms
open FStar.Ghost
open IntLib
 
(** Opaque integers **)
assume new type sint : Type0

(* Mathematical ghost value of the sint *)
assume val v: x:sint -> GTot int
let ssize (x:sint) (n:pos) : GTot Type0 = (v x >= -(pow2 (n-1)) /\ v x < pow2 (n-1))
let usize (x:sint) (n:nat)   : GTot Type0 = (v x >= 0 /\ v x < pow2 n)

(* Concrete types *)
type ssint (n:pos) = x:sint{ssize x n}
type usint (n:nat) = x:sint{usize x n}

(* Specs *)
assume val esmax_int: #n:pos -> Tot (max:erased nat{reveal max = pow2 (n-1) - 1})
assume val eumax_int: #n:nat -> Tot (max:erased nat{reveal max = pow2 n - 1})
assume val smax_int: #n:pos -> GTot (max:nat{max = pow2 (n-1) - 1})
assume val umax_int: #n:nat -> GTot (max:nat{max = pow2 n - 1})

assume val esmin_int: #n:pos -> Tot (min:erased nat{reveal min = - (pow2 (n-1))})
assume val eumin_int: #n:nat -> Tot (min:erased nat{reveal min = 0})
assume val smin_int: #n:pos -> GTot (min:nat{min = - (pow2 (n-1))})
assume val umin_int: #n:nat -> GTot (min:nat{min = 0})

(* Zero for signed and unsiged words *)
assume val szero: n:pos -> Tot (z:ssint n{v z = 0})
assume val uzero: n:nat -> Tot (z:usint n{v z = 0})
(* One for signed and unsigned words *)
assume val sone: n:pos{n > 1} -> Tot (o:ssint n{v o = 1})
assume val uone: n:pos -> Tot (o:usint n{v o = 1})
(* All ones mask for signed and unsigned words *)
assume val sones: n:pos{n > 1} -> Tot (o:ssint n{v o = -1})
assume val uones: n:pos -> Tot (o:usint n{v o = pow2 n - 1})

(* Increment and decrement *)
assume val sincr: #n:pos -> a:ssint n{v a < smax_int #n} -> Tot (b:ssint n{v b = v a + 1})
assume val uincr: #n:pos -> a:usint n{v a < umax_int #n} -> Tot (b:usint n{v b = v a + 1})
assume val spred: #n:pos -> a:ssint n{v a > smin_int #n} -> Tot (b:ssint n{v b = v a - 1})
assume val upred: #n:pos -> a:usint n{v a > umin_int #n} -> Tot (b:usint n{v b = v a - 1})

assume val sincr_mod: #n:pos -> a:ssint n -> Tot (b:ssint n{v b = cmod (v a + 1) (pow2 n)})
assume val uincr_mod: #n:pos -> a:usint n -> Tot (b:usint n{v b = (v a + 1) % (pow2 n)})
assume val spred_mod: #n:pos -> a:ssint n -> Tot (b:ssint n{v b = cmod (v a - 1) (pow2 n)})
assume val upred_mod: #n:pos -> a:usint n -> Tot (b:usint n{v b = (v a - 1) % (pow2 n)})

(* Addition primitives *)
assume val sadd: #n:pos -> a:ssint n ->
  b:ssint n{v a + v b < pow2 (n-1) /\ v a + v b >= - (pow2 (n-1))} ->
  Tot (c:ssint n{v c = v a + v b})
assume val sadd_mod: #n:pos -> a:ssint n -> b:ssint n ->
  Tot (c:ssint n{v c = cmod (v a + v b) (pow2 n)})
assume val uadd: #n:nat -> a:usint n -> b:usint n{v a + v b < pow2 n} ->
  Tot (c:usint n{v c = v a + v b})
assume val uadd_mod: #n:nat -> a:usint n -> b:usint n ->
  Tot (c:usint n{v c = (v a + v b) % (pow2 n)})

(* Subtraction primitives *)
assume val ssub: #n:pos -> a:ssint n ->
  b:ssint n{v a - v b >= - (pow2 (n-1)) /\ v a - v b < pow2 (n-1)} ->
  Tot (c:ssint n{v c = v a + v b})
assume val ssub_mod: #n:pos -> a:ssint n -> b:ssint n ->
  Tot (c:ssint n{v c = cmod (v a - v b) (pow2 n)})
assume val usub: #n:nat -> a:usint n -> b:usint n{v a - v b >= 0} ->
  Tot (c:usint n{v c = v a - v b})
assume val usub_mod: #n:nat -> a:usint n -> b:usint n ->
  Tot (c:usint n{v c = (v a - v b) % (pow2 n)})

(* Multiplication primitives *)
assume val smul: #n:pos -> a:ssint n ->
  b:ssint n{v a * v b < pow2 (n-1) /\ v a * v b >= - (pow2 (n-1))} ->
  Tot (c:ssint n{v c = v a * v b})
assume val smul_mod: #n:pos -> a:ssint n -> b:ssint n ->
  Tot (c:ssint n{v c = cmod (v a * v b) (pow2 n)})
assume val smul_large: #n:pos -> a:ssint n -> b:ssint n ->
  Tot (c:ssint (2*n){v c = v a * v b})
assume val umul: #n:nat -> a:usint n -> b:usint n{v a * v b < pow2 n} ->
  Tot (c:usint n{v c = v a * v b})
assume val umul_mod: #n:nat -> a:usint n -> b:usint n ->
  Tot (c:usint n{v c = (v a * v b) % (pow2 n)})
assume val umul_large: #n:pos -> a:usint n -> b:usint n ->
  Tot (c:usint (2*n){v c = v a * v b})

(* Division primitives *)
assume val sdiv: #n:pos -> a:ssint n ->
  b:ssint n{v b <> 0} -> Tot (c:ssint n{v c = div (v a) (v b)})
assume val udiv: #n:nat -> a:usint n -> b:usint n{v b <> 0} ->
  Tot (c:usint n{v c = v a / v b})

(* Modulo primitives *)
assume val smod: #n:pos -> a:ssint n ->
  b:ssint n{v b <> 0} -> Tot (c:ssint n{v c = div (v a) (v b)})
assume val umod: #n:nat -> a:usint n -> b:usint n{v b <> 0} ->
  Tot (c:usint n{v c = v a / v b})

(* Negation primitives *)
assume val sneg: #n:pos -> a:ssint n -> Tot (b:ssint n{v b = - (v a)})

(* Bitwise operators *)
assume val slogand: #n:pos -> ssint n -> ssint n -> Tot (ssint n)
assume val slogxor: #n:pos -> ssint n -> ssint n -> Tot (ssint n)
assume val slogor: #n:pos -> ssint n -> ssint n -> Tot (ssint n)
assume val slognot: #n:pos -> ssint n -> Tot (ssint n)
assume val ulogand: #n:nat -> usint n -> usint n -> Tot (usint n)
assume val ulogxor: #n:nat -> usint n -> usint n -> Tot (usint n)
assume val ulogor: #n:nat -> usint n -> usint n -> Tot (usint n)
assume val ulognot: #n:nat -> usint n -> Tot (usint n)

(* Bitwise operators lemmas *)
(* TODO: add reasonable patterns *)
(* TODO: find minimal subset *)
(* TODO: define a 'nth' function that returns the nth bit of the sint, and prove lemmas from it *)
assume val slogand_lemma_1: #n:pos -> a:ssint n -> b:ssint n ->
  Lemma (requires True) (ensures (v (slogand #n a b) = v (slogand #n b a)))
assume val slogand_lemma_2: #n:pos -> a:ssint n ->
  Lemma (requires True) (ensures (v (slogand #n a (szero n)) = 0))
assume val slogand_lemma_3: #n:pos{n > 1} -> a:ssint n ->
  Lemma (requires True) (ensures (v (slogand #n a (sones n)) = v a))

assume val slogxor_lemma_1: #n:pos -> a:ssint n -> b:ssint n ->
  Lemma (requires True) (ensures (v (slogxor #n a b) = v (slogxor #n b a)))
assume val slogxor_lemma_2: #n:pos -> a:ssint n ->
  Lemma (requires True) (ensures (v (slogxor #n a (szero n)) = v a))
assume val slogxor_lemma_3: #n:pos{n > 1} -> a:ssint n ->
  Lemma (requires True) (ensures (v (slogxor #n a (sones n)) = v (slognot #n a)))
assume val slogxor_lemma_4: n:pos -> a:ssint n ->
  Lemma (requires True) (ensures (v (slogxor #n a a) = 0))

assume val slogor_lemma_1: #n:pos -> a:ssint n -> b:ssint n ->
  Lemma (requires True) (ensures (v (slogor #n a b) = v (slogor #n b a)))
assume val slogor_lemma_2: #n:pos -> a:ssint n ->
  Lemma (requires True) (ensures (v (slogor #n a (szero n)) = v a))
assume val slogor_lemma_3: #n:pos{n > 1} -> a:ssint n ->
  Lemma (requires True) (ensures (v (slogor #n a (sones n)) = v (sones n)))

assume val slognot_lemma_1: #n:pos -> a:ssint n ->
  Lemma (requires True) (ensures (v (slognot #n (slognot #n a)) = v a))
assume val slognot_lemma_2: #n:pos{n > 1} ->
  Lemma (requires True) (ensures (v (slognot #n (szero n)) = v (sones n)))

assume val ulogand_lemma_1: #n:nat -> a:usint n -> b:usint n ->
  Lemma (requires True) (ensures (v (ulogand #n a b) = v (ulogand #n b a)))
assume val ulogand_lemma_2: #n:nat -> a:usint n ->
  Lemma (requires True) (ensures (v (ulogand #n a (uzero n)) = 0))
assume val ulogand_lemma_3: #n:pos -> a:usint n ->
  Lemma (requires True) (ensures (v (ulogand #n a (uones n)) = v a))
assume val ulogand_lemma_4: #n:nat -> a:usint n -> m:nat -> b:usint n ->
  Lemma (requires (v b = pow2 m - 1)) (ensures (v (ulogand #n a b) = v a % pow2 m))

assume val ulogxor_lemma_1: #n:nat -> a:usint n -> b:usint n ->
  Lemma (requires True) (ensures (v (ulogxor #n a b) = v (ulogxor #n b a)))
assume val ulogxor_lemma_2: #n:nat -> a:usint n ->
  Lemma (requires True) (ensures (v (ulogxor #n a (uzero n)) = v a))
assume val ulogxor_lemma_3: #n:pos -> a:usint n ->
  Lemma (requires True) (ensures (v (ulogxor #n a (uones n)) = v (ulognot #n a)))
assume val ulogxor_lemma_4: n:nat -> a:usint n ->
  Lemma (requires True) (ensures (v (ulogxor #n a a) = 0))

assume val ulogor_lemma_1: #n:nat -> a:usint n -> b:usint n ->
  Lemma (requires True) (ensures (v (ulogor #n a b) = v (ulogor #n b a)))
assume val ulogor_lemma_2: #n:nat -> a:usint n ->
  Lemma (requires True) (ensures (v (ulogor #n a (uzero n)) = v a))
assume val ulogor_lemma_3: #n:pos -> a:usint n ->
  Lemma (requires True) (ensures (v (ulogor #n a (uones n)) = v (uones n)))

assume val ulognot_lemma_1: #n:nat -> a:usint n ->
  Lemma (requires True) (ensures (v (ulognot #n (ulognot #n a)) = v a))
assume val ulognot_lemma_2: #n:pos ->
  Lemma (requires True) (ensures (v (ulognot #n (uzero n)) = v (uones n)))

(* Casts *)
assume val to_usint: m:nat -> a:sint -> Tot (b:usint m{v b = (v a) % pow2 m})
assume val to_ssint: m:pos -> a:sint -> Tot (b:ssint m{v b = cmod (v a) (pow2 m)})

(* Shift operators *)
assume val sshift_right: #n:pos -> a:ssint n -> s:nat ->
  Tot (b:ssint n{v b = div_eucl (v a) (pow2 s)})
assume val sshift_left: #n:pos -> a:ssint n -> s:nat ->
  Tot (b:ssint n{v b = cmod ((v a) * pow2 s) (pow2 n)})
assume val ushift_right: #n:nat -> a:usint n -> s:nat ->
  Tot (b:usint n{v b = div (v a) (pow2 s)})
assume val ushift_left: #n:nat -> a:usint n -> s:nat ->
  Tot (b:usint n{v b = ((v a) * pow2 s) % pow2 n})

val shift_right_logical: #n:pos -> a:ssint n -> s:nat -> Tot (ssint n)
let shift_right_logical #n a s =
  to_ssint n (ushift_right #n (to_usint n a) s)

assume val urotate_left: #n:nat -> a:usint n -> s:nat{s <= n} ->
  Tot (b:usint n{v b = (v a % pow2 (n - s)) * pow2 s + div (v a) (pow2 (n-s))})
assume val urotate_right: #n:nat -> a:usint n -> s:nat{s <= n} ->
  Tot (b:usint n{v b = (v a % pow2 s) * pow2 (n-s) + div (v a) (pow2 (s))})

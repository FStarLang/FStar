module Steel.CStdInt

module U32 = FStar.UInt32
module I32 = FStar.Int32

val size_t : Type0

val size_v (x: size_t) : GTot nat

val size_v_inj (x1 x2: size_t) : Lemma
  (size_v x1 == size_v x2 ==> x1 == x2)
  [SMTPat (size_v x1); SMTPat (size_v x2)]

val mk_size_t (x: U32.t) : Pure size_t
  (requires True)
  (ensures (fun y -> size_v y == U32.v x))

let zero_size : (zero_size: size_t { size_v zero_size == 0 }) = mk_size_t 0ul

let one_size : (zero_size: size_t { size_v zero_size == 1 }) = mk_size_t 1ul

val ptrdiff_t : Type0

module I32 = FStar.Int32

val ptrdiff_v (x: ptrdiff_t) : GTot int

val ptrdiff_v_inj (x1 x2: ptrdiff_t) : Lemma
  (ptrdiff_v x1 == ptrdiff_v x2 ==> x1 == x2)
  [SMTPat (ptrdiff_v x1); SMTPat (ptrdiff_v x2)]

val mk_ptrdiff_t (x: I32.t) : Pure ptrdiff_t
  (requires True)
  (ensures (fun y -> ptrdiff_v y == I32.v x))

let zero_ptrdiff : (zero_ptrdiff: ptrdiff_t { ptrdiff_v zero_ptrdiff == 0 }) =
  mk_ptrdiff_t 0l

val ptrdiff_precond (x: int) : Tot prop

val intro_ptrdiff_precond (x: int) : Lemma
  (requires (FStar.Int.size x I32.n))
  (ensures (ptrdiff_precond x))

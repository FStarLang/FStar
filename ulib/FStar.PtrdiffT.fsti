module FStar.PtrdiffT

module I16 = FStar.Int16
module I64 = FStar.Int64

val t : eqtype

val fits (x: int) : Tot prop

val v (x: t) : Ghost int
  (requires True)
  (ensures (fun y -> fits y))

val ptrdiff_v_inj (x1 x2: t) : Lemma
  (v x1 == v x2 ==> x1 == x2)
  [SMTPat (v x1); SMTPat (v x2)]

/// According to the C standard, "the bit width of size_t is not less than 16 since c99"
/// (https://en.cppreference.com/w/c/types/size_t)
/// As for size_t, we therefore offer two functions to create
/// a t value. Any value that fits in a uint_16 can be
/// cast directly to t
/// Any value that might not fit in a uint_16 needs to be checked,
/// we will add a static_assert during extraction
val mk (x: I16.t) : Pure t
  (requires True)
  (ensures (fun y -> v y == I16.v x))

val mk_checked (x: I64.t) : Pure t
  (requires True)
  (ensures (fun y -> v y == I64.v x))

let zero : (zero_ptrdiff: t { v zero_ptrdiff == 0 }) =
  mk 0s

val intro_ptrdiff_fits (x: int) : Lemma
  (requires (FStar.Int.size x I16.n))
  (ensures (fits x))

module Steel.CStdInt

module U64 = FStar.UInt64
module I64 = FStar.Int64
module Cast = FStar.Int.Cast

let size_t = U64.t

let size_v (x: size_t) : GTot nat =
  U64.v x

let size_v_inj (x1 x2: size_t) : Lemma
  (size_v x1 == size_v x2 ==> x1 == x2)
  [SMTPat (size_v x1); SMTPat (size_v x2)]
= ()

let mk_size_t (x: U32.t) : Pure size_t
  (requires True)
  (ensures (fun y -> size_v y == U32.v x))
= Cast.uint32_to_uint64 x

let ptrdiff_t = I64.t

let ptrdiff_v (x: ptrdiff_t) : GTot int =
  I64.v x

let ptrdiff_v_inj (x1 x2: ptrdiff_t) : Lemma
  (ptrdiff_v x1 == ptrdiff_v x2 ==> x1 == x2)
  [SMTPat (ptrdiff_v x1); SMTPat (ptrdiff_v x2)]
= ()

let mk_ptrdiff_t x = Cast.int32_to_int64 x

let ptrdiff_precond x = FStar.Int.fits x I64.n == true

let intro_ptrdiff_precond x = ()

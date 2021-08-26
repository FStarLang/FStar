module Steel.C.StdInt

module U64 = FStar.UInt64
module I64 = FStar.Int64
module Cast = FStar.Int.Cast

let size_t = U64.t

let size_precond x =
  FStar.UInt.fits x U64.n == true

let size_v x =
  U64.v x

let size_v_inj (x1 x2: size_t) : Lemma
  (size_v x1 == size_v x2 ==> x1 == x2)
  [SMTPat (size_v x1); SMTPat (size_v x2)]
= ()

let mk_size_t (x: U32.t) : Pure size_t
  (requires True)
  (ensures (fun y -> size_v y == U32.v x))
= Cast.uint32_to_uint64 x

let int_to_size_t x =
  U64.uint_to_t x

let size_precond_le x y = ()

let size_add x y = x `U64.add` y

let size_sub x y = x `U64.sub` y

let size_mul x y = x `U64.mul` y

let size_div x y = x `U64.div` y

let size_le x y = x `U64.lte` y

let ptrdiff_t = I64.t

let ptrdiff_v x =
  I64.v x

let ptrdiff_v_inj (x1 x2: ptrdiff_t) : Lemma
  (ptrdiff_v x1 == ptrdiff_v x2 ==> x1 == x2)
  [SMTPat (ptrdiff_v x1); SMTPat (ptrdiff_v x2)]
= ()

let mk_ptrdiff_t x = Cast.int32_to_int64 x

let ptrdiff_precond x = FStar.Int.fits x I64.n == true

let intro_ptrdiff_precond x = ()

module Steel.C.StdInt.Base

module I64 = FStar.Int64
module Cast = FStar.Int.Cast

(* FIXME: this could be defined as U64.t, but KReMLin currently demands U32.t.
   NS: A long-term proposal would be to make KReMLin platform-aware and introduce
   a platform switch in this library here.
*)

let size_t = U32.t

let size_precond x =
  FStar.UInt.fits x U32.n == true

let size_v x =
  U32.v x

let size_v_inj (x1 x2: size_t) : Lemma
  (size_v x1 == size_v x2 ==> x1 == x2)
  [SMTPat (size_v x1); SMTPat (size_v x2)]
= ()

let mk_size_t (x: U32.t) : Pure size_t
  (requires True)
  (ensures (fun y -> size_v y == U32.v x))
= x

let int_to_size_t x =
  U32.uint_to_t x

let size_precond_le x y = ()

let size_add x y = x `U32.add` y

let size_sub x y = x `U32.sub` y

let size_mul x y = x `U32.mul` y

let size_div x y = x `U32.div` y

let size_le x y = x `U32.lte` y

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

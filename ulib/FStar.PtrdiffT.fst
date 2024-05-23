module FStar.PtrdiffT

module Cast = FStar.Int.Cast
module I64 = FStar.Int64

open FStar.Ghost

friend FStar.SizeT

(** We assume the existence of lower and upper bounds corresponding to PTRDIFF_MIN
    and PTRDIFF_MAX, which ensure that a ptrdiff_t has at least width 16 according to
    the C standard *)
assume
val max_bound : x:erased int { x >= pow2 15 - 1 }
let min_bound : erased int = hide (- (reveal max_bound + 1))

(** We also assume that size_t is wider than ptrdiff_t *)
assume
val bounds_lemma (_:unit) : Lemma (SizeT.bound > max_bound)

let t = x:I64.t{I64.v x >= min_bound /\ I64.v x <= max_bound }

let fits x =
  FStar.Int.fits x I64.n == true /\
  x <= max_bound /\ x >= min_bound

let fits_lt x y = ()

let v x =
  I64.v x

let int_to_t (x: int) : Pure t
  (requires (fits x))
  (ensures (fun y -> v y == x))
  = I64.int_to_t x

let ptrdiff_v_inj x = ()
let ptrdiff_int_to_t_inj x = ()

let mk x = int_to_t (I16.v x)

let ptrdifft_to_sizet x =
  bounds_lemma ();
  SizeT.Sz <| Cast.int64_to_uint64 x

let add x y = I64.add x y

let div x y =
  FStar.Math.Lib.slash_decr_axiom (v x) (v y);
  I64.div x y

let rem x y = I64.rem x y
let gt x y = I64.gt x y
let gte x y = I64.gte x y
let lt x y = I64.lt x y
let lte x y = I64.lte x y

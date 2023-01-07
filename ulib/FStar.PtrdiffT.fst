module FStar.PtrdiffT

module Cast = FStar.Int.Cast
module I64 = FStar.Int64

let t = I64.t

let fits x = FStar.Int.fits x I64.n == true

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

let add = I64.add
let div x y = I64.div x y
let rem x y = I64.rem x y
let gt x y = I64.gt x y
let gte x y = I64.gte x y
let lt x y = I64.lt x y
let lte x y = I64.lte x y

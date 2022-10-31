module FStar.PtrdiffT

module Cast = FStar.Int.Cast

let t = I64.t

let fits x = FStar.Int.fits x I64.n == true

let v x =
  I64.v x

let ptrdiff_v_inj (x1 x2: t) = ()

let int_to_t (x: int) : Pure t
  (requires (fits x))
  (ensures (fun y -> v y == x))
  = I64.int_to_t x

let mk x = int_to_t (I16.v x)

let add = I64.add
let gt x y = I64.gt x y
let gte x y = I64.gte x y
let lt x y = I64.lt x y
let lte x y = I64.lte x y

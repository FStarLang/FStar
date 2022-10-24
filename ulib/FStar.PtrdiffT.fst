module FStar.PtrdiffT

module Cast = FStar.Int.Cast

let t = I64.t

let fits x = FStar.Int.fits x I64.n == true

let v x =
  I64.v x

let ptrdiff_v_inj (x1 x2: t) = ()

let mk x = Cast.int16_to_int64 x
let mk_checked x = x

let intro_ptrdiff_fits x = ()

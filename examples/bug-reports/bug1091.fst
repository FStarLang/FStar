module Bug1091

module UInt = FStar.UInt
module U64 = FStar.UInt64

type t = { low: U64.t; high: U64.t }

assume val v: t -> n:nat{n < pow2 128}

let logand (a b: t) : Pure t
  (requires True)
  (ensures (fun r -> v r = UInt.logand (v a) (v b))) = a

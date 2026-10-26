module ForeignProducer
module U32 = FStar.UInt32

let api (x:U32.t) : U32.t =
  let small = Foreign.identity x in
  let wide = Foreign.identity 0UL in
  if FStar.UInt64.eq wide 0UL
  then U32.add_mod (Foreign.hook () small) Foreign.value
  else 0ul

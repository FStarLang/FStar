module A
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.Int.Cast
module Cast = FStar.Int.Cast
let main argc argv = 
  if not (B.validate (Cast.int32_to_uint32 argc) argv)
  then 1l
  else 0l


module SGXState

open FStar.UInt64

let u64 = UInt64.t

type sgxstate =
 |Mksgxstate: read:(string -> u64) ->
  	      write:(string -> u64 -> unit)->
  	      load: (nat -> nat -> u64) ->
  	      store:(nat -> u64-> nat-> unit)->sgxstate 



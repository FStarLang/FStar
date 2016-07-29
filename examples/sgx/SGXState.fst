
module SGXState

open FStar.UInt64

let word = UInt64.t

type sgxstate =
 |Mksgxstate: read:(string -> word) ->
  	      write:(string -> word -> unit)->
  	      load: (nat -> nat -> word) ->
  	      store:(nat -> word-> nat-> unit)->
	      iscallableaddress:(nat->unit)->sgxstate 




module Bug122PatternsAreIncomplete

assume val bar : p:Type -> Tot bool

val foo : unit -> Tot bool
let foo x = (if bar False then true else false)

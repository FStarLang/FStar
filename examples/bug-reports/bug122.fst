
module Bug121PatternsAreIncomplete

assume val bar : p:Type -> Tot bool

val foo : unit -> Tot bool
let foo _ = (if bar False then true else false)

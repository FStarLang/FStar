
module Bug122PatternsAreIncomplete

assume val bar : p:Type -> Tot bool

val foo : unit -> Tot bool
let foo _ = (bar False then true else false)

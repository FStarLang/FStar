module Bug178

assume val verify: #p:(int -> Type) -> d:int -> Tot bool

assume new type pred (d:int)

val checkmail: int -> unit
let checkmail ctxt = if verify #pred ctxt then ()

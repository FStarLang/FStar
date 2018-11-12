module Bug1481

let (+) : bool -> bool -> bool = ( || )
let _ = assert (true + false == true)

let (&&) (p q : bool) : bool = p || q
let _ = assert ((true && false) == true)

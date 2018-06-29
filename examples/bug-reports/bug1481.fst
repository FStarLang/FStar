module Bug1481

let (+) : bool -> bool -> bool = ( || )
let _ = assert (true + false == true)

let (&&) : bool -> bool -> bool = ( || )
let _ = assert ((true && false) == true)

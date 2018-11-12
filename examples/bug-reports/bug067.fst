module Bug067

type good (i:int) (j:int) = True

val test : l1:int -> Tot (l2:int -> Tot (u:unit{good l1 l2}))
let test l1 l2 = ()
let x = assert True //only need this to trigger the encoding of what comes previously

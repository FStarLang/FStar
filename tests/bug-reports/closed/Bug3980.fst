module Bug3980

assume
val slprop : Type

assume
val p : int -> slprop

assume
val ( ** ) : slprop -> slprop -> slprop

let a = p 1 ** p 2 ** p 3
let b = p 1 ** (p 2 ** p 3)
let c = (p 1 ** p 2) ** p 3

#check p 1 ** p 2 ** p 3
#check (p 1 ** p 2) ** p 3
#check p 1 ** (p 2 ** p 3)

let _ = assert (a == b)

[@@expect_failure]
let _ = assert (a == c)
[@@expect_failure]
let _ = assert (b == c)

assume
val ( |-> ) : string -> int -> slprop

let _ = "a" |-> 1 ** "b" |-> 2


#check "a" |-> 1 ** "b" |-> 2

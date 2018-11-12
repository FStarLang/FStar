module Bug241

val test1 : (nat * unit)
let test1 = 2, ()

val test2 : (int * unit)
let test2 = test1

val coerce : (nat * unit) -> (int * unit)
let coerce p = let (x1,x2) = p in (x1,x2)

val test2' : (x:int * unit)
let test2' = coerce test1

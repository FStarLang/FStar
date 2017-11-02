module Bug607

// Not ok
type my_type (a:Type) (b:Type) = list (a * b)

val f: my_type int int -> unit
let f x = let rec helper (x: my_type int int) = x in ()

// Ok
type my_type2 (a:Type) (b:Type) = list (a * b)

val f2: my_type2 int int -> unit
let f2 x = let helper (x: my_type2 int int) = x in ()

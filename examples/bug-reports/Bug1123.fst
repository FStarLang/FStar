module Bug1123

assume val bar (x:int) :Dv unit

let foo (x:int) = bar x; Some #unit ()

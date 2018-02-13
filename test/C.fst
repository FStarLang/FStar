module C

open A
open B

let foo (x:int) = A.foo x + B.bar x

let bar (x:t1) :t1 = B.foo x

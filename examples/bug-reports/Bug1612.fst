module Bug1612
open FStar.Integers
assume val l : UInt32.t
let test (n:Prims.nat) = FStar.Integers.v l = n

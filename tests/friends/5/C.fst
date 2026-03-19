module C
friend B
friend A
let c = A.a + B.b + A.a_plus_one
let test = assert (c == 128)

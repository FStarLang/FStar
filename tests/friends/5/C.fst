module C
friend B
friend A
let c = A.a + B.b + A.internal_a + A.a_plus_one
let test = assert (c == 270)

module C
friend B
friend A
let c = A.a + B.b
let test = assert (c == 85)

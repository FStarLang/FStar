module C
friend A
friend B
let c = B.b + A.a
let test = assert (c == 1)

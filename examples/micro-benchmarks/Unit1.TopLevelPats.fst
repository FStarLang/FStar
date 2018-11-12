module Unit1.TopLevelPats

let (x, y) = (1, 2)
let _ = assert(x == 1)
let _ = assert(y == 2)

let make n = (n / 2, 3 `op_Multiply` n + 1)
let (z, w) = make 18
let _ = assert(z == 9)
let _ = assert(w == 55)

module Bug2172

// one existential quantification over two variables (`p2` below) is
// different from two extistential quantifications over one variable
// each (`p1` below)

let p1 = exists (x: int). exists (y: int). 0 == x + y
let p2 = exists (x: int)         (y: int). 0 == x + y

let _ = assert p1
let _ = assert p2
let _ = assert (p1 <==> p2)

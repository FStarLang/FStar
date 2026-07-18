module Bug2172
#push-options "--ext context_pruning"
// one existential quantification over two variables (`p2` below) is
// different from two existential quantifications over one variable
// each (`p1` below)
let p1 = exists (x: int). exists (y: int). 0 == x + y
let p2 = exists (x: int)         (y: int). 0 == x + y

let test0 (witness:nat) = assert p1
let test1 (x:int) = assert (0 == x + (-x)); assert p2
let _ = assert (p1 <==> p2)

#pop-options

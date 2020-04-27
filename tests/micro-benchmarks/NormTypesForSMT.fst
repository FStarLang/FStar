module NormTypesForSMT

let ta = (bool * (i:int{0 <= i /\ i <= 8}))
let tb = (bool * (i:int{0 <= i /\ i <= 9}))
let tc = (bool * (i:int{0 <= i /\ i <9+1}))
let td = (bool * (i:int{0 <= i /\ i < 10}))

let a:ta = (true, 5)
let a':ta = (true, 5)

let b:tb = (true, 5)
let b':tb = (true, 5)

let c:tc = (true, 5)
let c':tc = (true, 5)

let d:td = (true, 5)
let d':td = (true, 5)

let test () =
  assert (a == a');
  assert (b == b');
  assert (c == c');
  assert (d == d');
  assert (c == d);
  assert (c' == d');
  assert (c == d')

module Bug2014

private let _ = 2

private let (x,y) = (1,2)

let _ = assert (x == 1)
let _ = assert (y == 2)

(* x and y should be private and have the attr, sorry no actual testing of that *)

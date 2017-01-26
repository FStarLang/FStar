#push
module Interact
let x0 = 0
#end
#push
let x1 = 1
#end
#push
let x2 = 2
#end
#push
type t0 =
  | C0
  | C1
#end
#pop
#push
type t0 =
  | C0 : int -> t0
  | C1 : int -> t0
#end
#push
let f0 () = C0 x0
let f1 () = C1 x1
#end
#pop
#pop
#push
type t0 =
  | C0 : int * int -> t0
  | C1 : int * int -> t0
let f0 x = C0 (x0, x)
let f1 x = assert (x1=1); C1 (x1, x)
#end
#pop
#push
type t0 =
  | C0 : int * int -> t0
  | C1 : int * int -> t0
  | C2 : int * int -> t0
let f0 x = C0 (x0, x)
let f1 x = assert (x1=1); C1 (x1, x)
let f2 x = assert (x2=2); C2 (x1, x)
#end
#pop
#push
let z = assert (x2=1)
#end
#pop
#push
let z = assert (x2=2)
#end

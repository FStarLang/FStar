module Bug807b

#set-options "--print_implicits"

assume val t : int -> Type
assume val i : n:int -> t n

let test () (#x:int) : t x = i x
let y : t 42 = test ()
let z : t 42 = test () #_

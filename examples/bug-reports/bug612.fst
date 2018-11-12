module Bug612

val incr: x:int -> Pure int
  (requires True)
  (ensures  (fun r -> r = x + 1))
//let incr n = 0 // 1 error
let incr = function | _ -> 0 // 2 errors

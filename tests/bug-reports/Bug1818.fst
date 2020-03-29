module Bug1818

let test_t () = x:int -> Pure unit (requires x > 0) (ensures fun _ -> True)

assume val bar (x:int) : Pure unit (requires x > 0) (ensures fun _ -> True)

let foo () : (test_t ()) =
  fun x -> bar x

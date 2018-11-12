module Bug155

assume val pred: x:int -> Tot bool
assume val test: x:int -> Pure int
    (requires (True))
    (ensures (fun y -> pred y))
let test1 = assert (pred (test 0))

(* this works now *)
let test2' z = assert (pred (test z))

assume val myassert: b:Type -> Pure unit (requires (b)) (ensures (fun _ -> True))
assume val pred2: x:int -> Pure bool
    (requires (True))
    (ensures (fun y -> y))
let test2 x = myassert (b2t (pred2 x))

let test3 x = let y = pred2 x in assert y

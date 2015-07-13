module Bug155
assume val test: x:int -> Pure int
    (requires (True))
    (ensures (fun y -> y=x))

(* this fails *)
let test2 z = assert (test z = z)

(* this works *)
let test3 z = let y = test z in assert (y=z)

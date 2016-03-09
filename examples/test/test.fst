module Test
let f (x:int) = 
  x >= 0
  /\ (let y = x + 1 in 
     y >= 0)

let g x = assert (x=0)

(* let f (x:nat) (y:int) = x = y *)

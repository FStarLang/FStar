module Test2

let good (x:int) = x=0
assume val g : z:int{z=z /\ good z } -> Tot nat

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --log_queries"

val f1 : x:int -> Pure int (requires True) (ensures (fun y -> good (x + y)))
let f1 x =
  let y = if x = 0
	  then g (x - 1)
	  else 0 in
  -x

val f2 : x:int -> Pure int (requires True) (ensures (fun y -> good (x + y)))
let f2 x =
  let y = if x = 0
	  then g 0
	  else 0 in
  y + 1


val f3 : x:ref int -> ST int (requires (fun h -> True)) (ensures (fun h0 y h1 -> h0==h1 /\ (Heap.sel h0 x = y)))
let f3 x = 
  let y = if !x = 0
  	  then g (!x - !x)
  	  else 0 in
  !x + y


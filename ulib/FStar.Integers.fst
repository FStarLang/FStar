module FStar.Integers

#set-options "--initial_ifuel 1 --max_ifuel 1 --initial_fuel 0 --max_fuel 0"

let within_bounds (x:int) : prop = admit ()

let v (x:int)
  : Tot (y:int{(within_bounds y)})
  = admit ()

let foo (x:int) (y:int)
  : Tot (z:int{normalize (eq2 #int (v z) (v x + v y))})
  = admit ()
  
let bar (x:int)
  : Tot (z:int{v z == foo (v x) (v x)})
  = admit ()


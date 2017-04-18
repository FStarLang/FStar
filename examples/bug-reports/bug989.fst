module Bug989

let rec g (n:nat) =
  if n = 0 then true
  else g (n - 1)

#set-options "--initial_fuel 0 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
//#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let foo = assert (g 0 == true)


type t =
 | A
 | B

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 1"
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
let f (x:t) =
  match x with
  | A -> ()
  | B -> ()

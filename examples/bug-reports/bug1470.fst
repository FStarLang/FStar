module Bug1470

val length : list 'a -> Dv nat
let rec length l =
  match l with
  | [] -> 0
  | hd::tl -> 1 + length tl

assume val aux (n:int) :Dv nat

let length1 (n:int) :Dv nat = 1 + aux n

(*
 * From Kremlin test suite
 *)
open FStar.ST

assume val bar (_:unit) :St (x:int{x == 42})

assume val foo (x:int) :Pure int (requires True) (ensures (fun r -> r == x))

#set-options "--max_fuel 0 --max_ifuel 0"
let test () :St unit =
  let y = foo (bar ()) in
  assert (y == 42)

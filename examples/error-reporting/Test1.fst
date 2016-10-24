module Test1
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

//reports failing call to assert, and the failing formula
let test0 = assert (0==1)

//reports failing call to assert, and the 1st conjunct of the failing formula
let test1 = assert (0==1 /\ 0==0)


assume val test2_aux: x:int -> Pure int (requires (x >= 0) /\ 0=0 )
				    (ensures (fun x -> True))
let test2 (x:int) =
  let y = test2_aux x in //reports failing call, and the definition site of the relevant conjunct of requires clause
  y + 1

let test3 x =
  let f = test2_aux in //local renaming
  let y = f (-1) in       //should still report this location
  y + 1

assume val test4_aux: nat -> Tot int
let test4 (x:int) =
  let y = test4_aux x in //subtyping check failed, expected nat, got int
  y + 1

val test5: x:int -> Pure int (requires (b2t (x <> 0))) (ensures (fun x -> 0 >= 0 /\ x >= 0))
let test5 x = x + 1


(* let (x:int) = False *)
(* val main: int -> Tot int *)

(* assume val test1: x:int -> Pure int (requires (good x)) *)
(* 			       (ensures (fun x -> True)) *)

(* val main: int -> Tot int *)
(* let main x = *)
(*   let f = test0 in *)
(*   let w = test0 x in *)
(*   let y = f w in *)
(*   let zz = test1 x in *)
(*   let z = test0 (op_Multiply y y) in *)
(*   z *)

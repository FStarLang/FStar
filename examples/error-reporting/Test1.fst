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
let test5 x = x + 1 //reports failing 2nd conjunct of post-condition


val test6: unit -> Lemma (0==1)
let test6 () = () //reporting a failing post-condition

//!!!!!!!!!!!!!!!!!!!!!!!!
// reports a terrible location in prims, because of an optimization
// that blows away most of the VC because of the False post-condition
//!!!!!!!!!!!!!!!!!!!!!!!!
val test7: unit -> Lemma False
let test7 () = ()

assume val test8_aux: x:nat -> Tot nat
let test8 (x:int{test8_aux x = 0}) = () //reports expected nat; got int

assume val test9_aux : x:int -> Pure bool (requires (b2t (x >= 0))) (ensures (fun x -> True))
assume val test9 : x:int{test9_aux x} -> Tot unit //should report a failing assertion in the refinement (f x)

#set-options "--detail_errors"
assume val p1 : bool
let p2 = true
assume val p3 : bool
assume val p4 : bool

let test10 = 
  assert p1;
  assert p2;
  assert p3;
  assert (p2 \/ p3)

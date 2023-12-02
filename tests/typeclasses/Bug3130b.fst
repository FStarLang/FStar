module Bug3130b

(* This never actually regressed, but it's a decent test anyway *)

open FStar.Tactics

assume val it : int -> Type0
assume val mk5 : (#[exact (`5)] x:int) -> it x
assume val mk6 : (#[exact (`6)] x:int) -> it x

let test0 = mk5
let test1 = mk6

let test2 (y : it 6) = let p : Type0 = mk5 == y in ()
let test3 (y : it 6) = let p : Type0 = y == mk5 in ()
let test4 (y : it 6) = let p : Type0 = mk6 == y in ()
let test5 (y : it 6) = let p : Type0 = y == mk6 in ()

let test6 () = let p : Type0 = mk5 == mk6 in ()
let test7 () = let p : Type0 = mk6 == mk5 in ()

let test8 (x:_) = let p : Type0 = mk5 == x /\ x == mk6 in ()
let test9 (x:_) = let p : Type0 = mk6 == x /\ x == mk5 in ()

module Coercions1Phase

(* This file should be in sync with Coercions.fst *)

(* Except that we disable two phase tc here *)
#set-options "--use_two_phase_tc false"

open FStar.Ghost

[@(expect_failure [34])]
let test0 (x: erased int) : Tot int = x

let test1 (x: erased int) : GTot int = x

let test2 (x:int) : erased int = x

let test3 (x:erased int) : erased int = x

let test4 (x:erased int) : GTot (erased int) = x

let test5 (x:int) : GTot (erased int) = x

[@(expect_failure [34])]
let test0' (x: erased 'a) : Tot 'a = x

let test1' (x: erased 'a) : GTot _ = x

(* let test2' (x:'a) : erased _ = x *)

let test3' (x:erased 'a) : erased _ = x

let test4' (x:erased 'a) : GTot (erased _) = x

(* let test5' (x:'a) : GTot (erased _) = x *)

let test1'' (x: erased 'a) : GTot 'a = x

let test2'' (x:'a) : erased 'a = x

let test3'' (x:erased 'a) : erased 'a = x

let test4'' (x:erased 'a) : GTot (erased 'a) = x

let test5'' (x:'a) : GTot (erased 'a) = x

assume val p : int -> prop
assume val foo (x:int) : Lemma (ensures (p x))

let bar (x:erased int) : Tot unit =
  foo (reveal x);
  assert (p (reveal x))

let test_bar (x:erased int) : Tot unit =
  foo x;
  assert (p x)

module Fib

open LowComp
open HighComp

open FStar.UInt32

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module U32 = FStar.UInt32



(** Slow, recursive defintion of fib *)
let rec fib (n : int) : Tot mint (decreases n) = 
  if n <= 0 then 0ul
  else if n = 1 then 1ul
  else 
    let f1 : mint = fib (n - 1) in
    let f2 : mint = fib (n - 2) in 
    f1 +%^ f2


let inv (s : state) (i:int) = i >= 1 /\ (fst s = fib (i - 1) /\ snd s = fib i)


let shift i : Hi unit (fun s0 -> inv s0 i)
                      (fun s0 () s1 -> inv s1 (i + 1)) = 
  let x0 = get_action 0 in
  let x1 = get_action 1 in
  let _  = put_action 0 x1 in 
  let _  = put_action 1 (x0 +%^ x1) in
  ()


let fib_fast n : Hi mint (fun s0 -> True) (fun s0 r s1 -> r = fib n) = 
    if (n <= 0) then 0ul
    else 
      begin 
        put_action 0 0ul; // 0 has fib 0
        put_action 1 1ul; // 1 has fib 1
        for' inv shift 1 n;
        get_action 1
      end


(* from example1.fst *)
let morph #a (#wp:hwp_mon a) ($c:HIGH?.repr a wp) : lcomp_wp a wp c = morph #a wp c

let fib_low n = morph (reify (fib_fast n))


                      

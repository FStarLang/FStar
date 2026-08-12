module Bench.Dead
open FStar.List.Tot
#set-options "--z3rlimit 60"
let rec upto (n:nat) : list int = if n = 0 then [] else n :: upto (n-1)
let rec sum (l:list int) : int = match l with | [] -> 0 | x::xs -> x + sum xs
let konst (x:int) (y:int) : int = x
#push-options "--no_smt"
let _ = assert_norm (konst 7 (sum (upto 6000)) == 7)
#pop-options

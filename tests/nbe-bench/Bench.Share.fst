module Bench.Share
open FStar.List.Tot
#set-options "--z3rlimit 30"
let rec upto (n:nat) : list int = if n = 0 then [] else n :: upto (n-1)
let rec sum (l:list int) : int = match l with | [] -> 0 | x::xs -> x + sum xs
let f (a b c d : int) : int = a + b + c + d
#push-options "--no_smt"
let _ = assert_norm ((let big = sum (upto 400) in f big big big big) == 320800)
#pop-options

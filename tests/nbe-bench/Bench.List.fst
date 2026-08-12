module Bench.List
open FStar.List.Tot
#set-options "--z3rlimit 30"

let rec upto (n:nat) : list int = if n = 0 then [] else n :: upto (n-1)
let rec sum (l:list int) : int = match l with | [] -> 0 | x::xs -> x + sum xs

#push-options "--no_smt"
let _ = assert_norm (sum (map (fun (x:int) -> x + 1) (upto 800)) == 321200)
let _ = assert_norm (length (append (upto 500) (rev (upto 500))) == 1000)
let _ = assert_norm (sum (filter (fun (x:int) -> x % 2 = 0) (upto 800)) == 160400)
#pop-options

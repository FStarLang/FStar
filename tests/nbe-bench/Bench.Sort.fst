module Bench.Sort
open FStar.List.Tot
#set-options "--z3rlimit 30"

let rec gen (n:nat) (s:int) : list int =
  if n = 0 then [] else ((s * 7919 + 13) % 1000) :: gen (n-1) ((s * 7919 + 13) % 1000)
let rec ins (x:int) (l:list int) : list int =
  match l with | [] -> [x] | y::ys -> if x <= y then x::y::ys else y :: ins x ys
let rec isort (l:list int) : list int =
  match l with | [] -> [] | x::xs -> ins x (isort xs)
let rec sorted (l:list int) : bool =
  match l with | [] -> true | [_] -> true | x::y::r -> x <= y && sorted (y::r)

#push-options "--no_smt"
let _ = assert_norm (sorted (isort (gen 250 1)) == true)
#pop-options

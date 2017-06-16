module Seq.Complements

open FStar.Seq

let _in (s:seq 'a) = k:nat{k < length s}
let ( @^ ) (s:seq 'a) (i:_in s) : 'a = index s i
let snoc (s:seq 'a) (x:'a) = s `append` (create 1 x)

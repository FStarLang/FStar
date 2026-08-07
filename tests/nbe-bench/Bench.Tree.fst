module Bench.Tree
#set-options "--z3rlimit 30"

type tree =
  | Leaf : tree
  | Node : tree -> int -> tree -> tree

let rec build (d:nat) (v:int) : tree =
  if d = 0 then Leaf else Node (build (d-1) (2*v)) v (build (d-1) (2*v+1))
let rec tsum (t:tree) : int =
  match t with | Leaf -> 0 | Node l v r -> tsum l + v + tsum r

#push-options "--no_smt"
let _ = assert_norm (tsum (build 12 1) == 8386560)
#pop-options

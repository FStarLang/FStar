module Bench.HO
open FStar.List.Tot
#set-options "--z3rlimit 30"
let rec upto (n:nat) : list int = if n = 0 then [] else n :: upto (n-1)
let compose (#a #b #c:Type) (f:b -> c) (g:a -> b) : a -> c = fun x -> f (g x)
let rec iterate (#a:Type) (n:nat) (f:a -> a) : a -> a =
  if n = 0 then (fun x -> x) else compose f (iterate (n-1) f)
#push-options "--no_smt"
let _ = assert_norm (iterate 400 (fun (x:int) -> x + 1) 0 == 400)
let _ = assert_norm (fold_left (fun (a:int) (x:int) -> a + x) 0 (upto 600) == 180300)
#pop-options

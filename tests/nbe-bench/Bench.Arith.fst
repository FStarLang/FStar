module Bench.Arith
#set-options "--z3rlimit 30"
let rec fib (n:nat) : nat = if n < 2 then n else fib (n-1) + fib (n-2)
let rec ack (m:nat) (n:nat) : Tot nat (decreases %[m;n]) =
  if m = 0 then n+1 else if n = 0 then ack (m-1) 1 else ack (m-1) (ack m (n-1))
#push-options "--no_smt"
let _ = assert_norm (fib 24 == 46368)
let _ = assert_norm (ack 2 6 == 15)
#pop-options

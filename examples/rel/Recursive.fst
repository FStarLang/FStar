module Recursive 
(* Reasoning about recursive functions *)

#set-options "--initial_fuel 1"

val fac : nat -> Tot nat 
let rec fac i = if i = 0 then 1 else op_Multiply (fac (i-1)) i

val fac_mon : n:nat -> m:nat -> 
  Lemma 
    (requires (n >= m))
    (ensures  (fac n >= fac m))
let rec fac_mon  n m = 
  match n, m with 
  | 0, 0 -> ()
  | _, 0 -> fac_mon (n-1) m
  | _, _ -> fac_mon (n-1) (m-1)

(* Lemmas can be applied to prove properties about larger functions *)

val fac_sum : nat -> nat -> Tot nat 
let fac_sum n m = fac n + fac m

val fac_sum_mon : n:nat -> m:nat -> n':nat -> m':nat ->
  Lemma 
    (requires (n >= n' /\ m >= m'))
    (ensures  (fac_sum n m >= fac_sum n' m'))
let fac_sum_mon n m n' m'= fac_mon n n'; fac_mon m m'

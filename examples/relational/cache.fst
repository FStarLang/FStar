(*--build-config
    options:--admit_fsi Set;
    variables:LIB=../../lib;
    other-files:$LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/st2.fst $LIB/list.fst
  --*)

module Cache

open Relational
open Comp
open Heap
open List

val fib : nat -> Tot nat
let rec fib x = if x <= 1 then 1 else  fib (x-1) + fib (x-2)

type fib_cache = list (nat * nat)
assume val cache : ref fib_cache

type fib_cache_correct (c:fib_cache) = (forall x. is_Some (assoc x c) ==> (Some.v (assoc x c) = fib x))

(*
val fib_cached : x:nat -> ST nat (requires (fun h -> fib_cache_correct (sel h cache)))
                               (ensures  (fun _ r h ->  fib_cache_correct (sel h cache)
                                                        /\ r = fib x))
*)
let (fib_cached x):nat =
  let c = !cache in
  let l = assoc x c in
  if is_Some l then
    Some.v l
  else(
    let v = fib x in
    cache := (x,v) :: c;
    fib x)

val correct : eq nat
  -> ST2 (eq nat)
         (requires (fun h -> fib_cache_correct (sel (R.r h) cache)))
         (ensures (fun _ _ h -> fib_cache_correct (sel (R.r h) cache)))
let correct x = compose2 (fun x -> fib x) (fun x -> fib_cached x) x

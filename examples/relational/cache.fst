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

(* Functional Sepcification of Factorials *)
val fac : nat -> Tot nat
let rec fac x = if x = 0 then 1 else  fac (x-1) * x

(* A tail-recursive imperative implementation *)
val imp_fac : x:ref nat -> a:ref nat 
  -> ST nat (requires (fun h -> a <> x))
            (ensures  (fun h r h' -> a <> x 
                                  /\ r = (fac (sel h x) * (sel h a))
                                  /\ sel h' x = 0 
                                  /\ sel h' a = r
                                  /\ modifies (a ^+^ x) h h'))
let rec imp_fac x a = 
  if !x = 0 then 
    !a 
  else 
  ( a := !a * !x;
    x := !x -1;
    imp_fac x a)

(* A wrapper for the recursive function, ensuring that the heap will not be
   modified *)
val imp_fac_wrap : x:ref nat -> a:ref nat -> y:nat 
  -> ST nat (requires  (fun h -> a <> x))
            (ensures   (fun h r h' -> r = fac y 
                                       /\ modifies Set.empty h h'))
let imp_fac_wrap x a y =
  let tmp1 = !x in 
  let tmp2 = !a in
  x := y;
  a := 1;
  let res = imp_fac x a in 
  x := tmp1;
  a := tmp2;
  res

type fac_cache = list (nat * nat)
assume val cache : ref fac_cache

(* An invariant on the correctness of the cache *)
type fac_cache_correct (c:fac_cache) = (forall x. is_Some (assoc x c) ==> (Some.v (assoc x c) = fac x))

(* A cached version of the factorial computation *)
val fac_cached : x:nat -> ST nat (requires (fun h -> fac_cache_correct (sel h cache)))
                                 (ensures  (fun h r h' ->  fac_cache_correct (sel h' cache)
                                                        /\ modifies (only cache) h h'
                                                        /\ r = fac x))
let fac_cached x =
  let c = !cache in
  let l = assoc x c in
  if is_Some l then
    Some.v l
  else(
    let v = fac x in
    cache := (x,v) :: c;
    fac x)

(* Can we maybe proof this? (modifies is defined based on equality..) *)
(* Maybe it is also better to define an own predicate for this, because we are
   somehow "abusing" modifies for a different purpose *)
assume val heap_modifies_refl : h0:heap -> h1:heap -> mods:Set.set Heap.aref
  -> Lemma (requires (modifies mods h0 h1))
           (ensures  (modifies mods h1 h0))
(* let heap_modifies_refl h0 h1 mods = () *)

(* Proof that the functions compute the same values and that cache is the only
   memory cell that can be modified *)
val correct : x:ref nat -> a:ref nat -> y:eq nat
  -> ST2 (eq nat)
         (requires (fun h -> fac_cache_correct (sel (R.r h) cache)
                          /\ x <> a 
                          /\ modifies (only cache) (R.l h) (R.r h)))
         (ensures (fun h _ h' -> fac_cache_correct (sel (R.r h') cache)
                              /\ modifies (only cache) (R.l h') (R.r h')))
let correct x a y =   let h = compose2_self ST.get (twice ()) in 
                      let res = compose2 (fun y -> imp_fac_wrap x a y) (fun x -> fac_cached x) y in
                      let h' = compose2_self ST.get (twice ()) in 
                      heap_modifies_refl (R.l h) (R.l h') (Set.empty);
                      res

(*--build-config
    options:--admit_fsi FStar.Set --z3timeout 5;
    other-files:FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Relational.fst FStar.List.fst
  --*)

module Cache

open FStar.Relational
open FStar.Comp
open FStar.List
open FStar.Heap

(* Functional Sepcification of Factorials *)
val fac : nat -> Tot nat
let rec fac x = if x = 0 then 1 else  fac (x-1) * x

(* A tail-recursive imperative implementation *)
val imp_fac : x:ref nat -> a:ref nat
  -> ST nat (requires (fun h -> a <> x
                             /\ contains h a
                             /\ contains h x ))
            (ensures  (fun h r h' -> a <> x
                                  /\ r = (fac (sel h x) * (sel h a))
                                  /\ sel h' x = 0
                                  /\ sel h' a = r
                                  /\ equal h' (upd (upd h x 0) a r)))
let rec imp_fac x a =
  if !x = 0 then
    !a
  else
  ( a := !a * !x;
    x := !x - 1;
    imp_fac x a
    )


(* A wrapper for the recursive function, ensuring that the heap will not be
   modified *)
val imp_fac_wrap : x:ref nat -> a:ref nat -> y:nat
  -> ST nat (requires  (fun h -> a <> x
                              /\ contains h a
                              /\ contains h x ))
            (ensures   (fun h r h' -> r = fac y
                                   /\ equal h h'))
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
val fac_cached : x:nat -> ST nat (requires (fun h -> fac_cache_correct (sel h cache)
                                                  /\ contains h cache))
                                 (ensures  (fun h r h' ->  fac_cache_correct (sel h' cache)
                                                        /\ (exists c. equal h' (upd h cache c))
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

(* Proof that the functions compute the same values and that cache is the only
   memory cell that can be different in the two runs *)
val correct : x:ref nat -> a:ref nat -> y:eq nat
  -> ST2 (eq nat)
         (requires (fun h -> fac_cache_correct (sel (R.r h) cache)
                          /\ x <> a
                          /\ contains (R.l h) x
                          /\ contains (R.l h) a
                          /\ contains (R.r h) cache
                          /\ (exists c. equal (upd (R.l h) cache c) (R.r h))))
         (ensures (fun h _ h' -> fac_cache_correct (sel (R.r h') cache)
                              /\ (exists c. equal (upd (R.l h') cache c) (R.r h'))))
let correct x a y =  compose2 (fun y -> imp_fac_wrap x a y) (fun x -> fac_cached x) y

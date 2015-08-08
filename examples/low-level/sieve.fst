(*--build-config
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/set.fst $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/list.fst  stack.fst listset.fst
    $LIB/ghost.fst stackAndHeap.fst sst.fst sstCombinators.fst $LIB/seq.fsi $LIB/seq.fst array.fsi array.fst arrayalgos.fst sieveFun.fst
  --*)

module Sieve
open SSTCombinators
open StackAndHeap
open SST
open Heap
open Stack
open Set
open Prims
open List
open ListSet
open Ghost
(*val divides : pos -> nat -> Tot bool
let divides divisor n = ((n % divisor) = 0)*)
(*Instead, below is a definition from first principles*)
open ArrayAlgos
open SSTArray

type bitarray = sstarray bool


open SSTArray

(* val mark : n:nat -> ((k:nat{k<n}) -> Tot bool) -> index:nat{index<n} -> Tot ((k:nat{k<n}) -> Tot bool) *)
let mark f index =
  writeIndex f index true


val bvAsFun : n:nat -> m:smem -> b:bitarray{haslength m b n} -> Tot (erased ((k:nat{k<n}) -> Tot bool))
let bvAsFun n m b = arrayAsFun n m b

val bvAsFun2 : n:nat -> m:smem -> b:bitarray{haslength m b n} -> k:nat{k<n} -> Tot (erased bool)
let bvAsFun2 n m b k = elift1 (fun (f:((k:nat{k<n}) -> Tot bool)) -> f k) (bvAsFun n m b)


type  innerLoopInv (n:nat) (lo: ref nat)  (li : ref nat) (res: (sstarray bool))
    (initres: ((k:nat{k<n}) -> Tot bool)) (m:smem) =
 SieveFun.distinctRefsExists3 m lo (reveal (asRef res)) li
  /\ 1 < (loopkupRef li m) /\  haslength m res n
  /\ SieveFun.markedIffMultipleOrInit n (loopkupRef lo m) (loopkupRef li m) initres (reveal (bvAsFun n m res))

val innerLoop : n:nat{n>1}
  -> lo: ref nat
  -> li : ref nat
  -> res : bitarray
  -> initres : ((k:nat{k<n}) -> Tot bool)
  -> Mem unit
      (requires (fun m -> innerLoopInv n lo li res initres m /\
        haslength m res n /\
        loopkupRef li m = 2  /\ 1 < (loopkupRef lo m)
                    /\ (forall k. (reveal (bvAsFun2 n m res k)  = initres k)) ))
      (ensures (fun _ _ m -> SieveFun.distinctRefsExists3 m lo (reveal (asRef res)) li
                /\ haslength m res n
                /\ SieveFun.markedIffDividesOrInit2 n (loopkupRef lo m) initres (reveal (bvAsFun n m res))
      ))
      ((elift2 union) (gonly li)  (ArrayAlgos.eonly res))

let innerLoop n lo li res initres =
  (scopedWhile
    (innerLoopInv n lo li res initres)
    (SieveFun.innerGuardLC n lo li)
    (fun u -> (memread li * memread lo < n))
      ((elift2 union) (gonly li)  (ArrayAlgos.eonly res))
    (fun u ->
      let liv = memread li in
      let lov = memread lo in
      memwrite li (liv+1);
      mark res (lov * liv)))

    (*the part below has no computaional content; why does SMTPatT not work?*)
      let newv = memread res in
      let lov = memread lo in
      (SieveFun.multiplesMarkedAsDividesIff n initres newv lov)

type  outerLoopInv (n:nat) (lo: ref nat) (res:ref ((k:nat{k<n}) -> Tot bool)) (m:smem) =
 distinctRefsExists2 m lo res
  /\ (((loopkupRef lo m) - 1) < n)
  /\ (1<(loopkupRef lo m))
  /\ (markedIffHasDivisorSmallerThan n (loopkupRef lo m) (loopkupRef res m))


(*#set-options "--initial_fuel 100 --max_fuel 10000 --initial_ifuel 100 --max_ifuel 10000"*)

val outerLoopBody :
  n:nat{n>1}
  -> lo:(ref nat)
  -> res : ref ((k:nat{k<n}) -> Tot bool)
  -> unit ->
  whileBody
    (outerLoopInv n lo res)
    (outerGuardLC n lo)
    (hide (union (singleton (Ref lo)) (singleton (Ref res))))


let outerLoopBody n lo res u =
  (*pushStackFrame ();*)
  let initres = memread res in
  let lov = memread lo in
  let li = salloc 2 in
  let liv = memread li in
  innerLoop n lo li res initres;
  let newres = memread res in
  memwrite lo (lov+1);
  (*the part below has no computational content*)
  (markedIffHasDivisorSmallerThanInc n lov initres newres)

val outerLoop : n:nat{n>1}
  -> lo: ref nat
  -> res : ref ((k:nat{k<n}) -> Tot bool)
  -> Mem unit
      (fun m -> distinctRefsExists2 m lo res /\ loopkupRef lo m =2 /\ allUnmarked n (loopkupRef res m))
      (fun m0 _ m1 ->
            distinctRefsExists2 m1 lo res
            /\ sids m0 = sids m1
           /\ (markedIffHasDivisorSmallerThan n n (loopkupRef res m1))
      )
      (hide (union (singleton (Ref lo)) (singleton (Ref res))))

let outerLoop n lo res =
  scopedWhile
    (outerLoopInv n lo res)
    (outerGuardLC n lo)
    (fun u -> (memread lo < n))
    (hide (union (singleton (Ref lo)) (singleton (Ref res))))
    (outerLoopBody n lo res)

val sieve : n:nat{n>1} -> unit
  -> WNSC ((k:nat{k<n}) -> Tot bool)
        (requires (fun m -> True))
        (ensures (fun _ resv _ -> markedIffHasDivisorSmallerThan n n resv))
        (hide empty)
let sieve n u =
  let lo = salloc 2 in
  let f:((k:nat{k<n}) -> Tot bool) = (fun x -> false) in
  let res = salloc f in
  (outerLoop n lo res);
  //assert (False);
  memread res

val sieveFull : n:nat{n>1}
  -> Mem ((k:nat{k<n}) -> Tot bool)
        (requires (fun m -> True))
        (ensures (fun _ resv _ -> markedIffHasDivisorSmallerThan n n resv))
        (hide empty)
let sieveFull n =
  pushStackFrame ();
  let res= sieve n () in
  popStackFrame (); res

val firstN : n:nat -> Tot (list nat)
let rec firstN n = match n with
| 0 -> []
| _ -> (n-1)::(firstN (n-1))

val toBool : n:nat{n>1} -> ((k:nat{k<n}) -> Tot bool) -> Tot (list bool)
let toBool n f = mapT (fun (x:nat) -> if x < n then f x else false) (firstN n)

(*let sieveFullTypeInfFail n= withNewScope #empty (sieve n)*)
val listOfTruesAux : n:nat -> max:nat{max<=n} -> f:((k:nat{k<n}) -> Tot bool) -> Tot (list nat)
let rec listOfTruesAux n max f = if (max<=2) then [] else
  ( if not (f (max-1)) then ((max-1)::(listOfTruesAux n (max - 1) f)) else (listOfTruesAux n (max - 1) f))

val listOfTrues : n:nat  -> f:((k:nat{k<n}) -> Tot bool) -> Tot (list nat)
let listOfTrues n f = listOfTruesAux n n f

val sieveAsList : n:nat{n>1}
  -> Mem (list nat)
        (requires (fun m -> True))
        (ensures (fun _ resv _ -> True))
        (hide empty)
let sieveAsList n =
  let sieveRes = (sieveFull n) in
  listOfTrues n sieveRes

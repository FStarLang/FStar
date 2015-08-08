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


type bitv n = b:(Seq.seq bool){Seq.length b =n}

val marked : n:nat -> b:(bitv n) -> m:nat{m<n} -> Tot bool
let marked n f m = (Seq.index f m)


type markedIffMultipleOrInit (n:nat) (lo:nat) (upto:nat)
  (init:bitv n) (neww:bitv n) =
  (forall (k:nat{k < upto /\ 1<k /\ lo*k<n}). marked n neww (lo*k))
  /\ (forall (m:nat{m < n}). (marked n init m ==> marked n neww m))
  /\ (forall (m:nat{m < n}). (marked n neww m ==> (marked n init m \/
      SieveFun.nonTrivialDivides lo m) ))

type  innerLoopInv (n:nat) (lo: ref nat)  (li : ref nat) (res: bitarray)
    (initres: erased (bitv n)) (m:smem) =
 SieveFun.distinctRefsExists3 m lo (reveal (asRef res)) li
  /\ 1 < (loopkupRef li m) /\  haslength m res n
   /\ markedIffMultipleOrInit n (loopkupRef lo m) (loopkupRef li m) (reveal initres) (reveal (esel m res))


type markedIffDividesOrInit2 (n:nat) (lo:nat)
   (init:bitv n) (newres: bitv n) =
   (forall (k:nat{k * lo < n /\ 1<k}). marked n newres (lo*k))
   /\ (forall (m:nat{m < n}). (marked n init m ==> marked n newres m))
   /\ (forall (m:nat{m < n}). (marked n newres m ==> (marked n init m \/
         SieveFun.nonTrivialDivides lo m
     )))

type markedIffDividesOrInit (n:nat) (lo:nat)
  (init: bitv n) (neww:bitv n) =
   (forall (k:nat{k < n}). (marked n neww k <==> (marked n init k \/ SieveFun.nonTrivialDivides lo k)))


type multiplesMarked (n:nat) (biv : bitv n) (lo:nat) =
  (forall (m:nat{m<n}). (SieveFun.nonTrivialDivides lo m) ==> marked n biv m)
 (* this works, is totally precise, but is hard to use
 /\ loopkupRef res m = markMultiplesUpto n lov (loopkupRef li m) initres*)

       (*(k < (loopkupRef li m))
           ==> (marked n (loopkupRef res m) ((loopkupRef lo m)*k)))*)

type multiplesMarked2 (n:nat) (bv : bitv n) (lo:nat) =
 (forall (k:nat). (k * lo < n /\ 1<k)  ==> marked n bv (lo*k))

val multiplesMarkedAsDivides :
 n:nat -> bitv:(erased (bitv n)) -> lo:pos
 -> Lemma
   (requires (multiplesMarked2 n (reveal bitv) lo))
   (ensures (multiplesMarked n (reveal bitv) lo))
let multiplesMarkedAsDivides n bitv lo = ()


val multiplesMarkedAsDividesIff :
 n:nat -> initv:(erased (bitv n)) -> newv:(erased (bitv n)) -> lo:pos
 -> Lemma
   (requires (markedIffDividesOrInit2 n lo (reveal initv) (reveal newv)))
   (ensures (markedIffDividesOrInit n lo (reveal initv) (reveal newv)))

      [SMTPatT (markedIffDividesOrInit n lo (reveal initv) (reveal newv))]

let multiplesMarkedAsDividesIff n initv newv lo = (multiplesMarkedAsDivides n newv lo)

val innerLoop : n:nat{n>1}
  -> lo: ref nat
  -> li : ref nat
  -> res : bitarray
  -> initres : (erased (bitv n))
  -> Mem unit
      (requires (fun m -> innerLoopInv n lo li res initres m /\
        haslength m res n /\
        loopkupRef li m = 2  /\ 1 < (loopkupRef lo m)
                    /\ reveal (esel m res)  = reveal initres ))
      (ensures (fun _ _ m -> SieveFun.distinctRefsExists3 m lo (reveal (asRef res)) li
                /\ haslength m res n
                /\ markedIffDividesOrInit2 n (loopkupRef lo m) (reveal initres) (reveal (esel m res))
                (* markedIffDividesOrInit n (loopkupRef lo m) initres (reveal (esel m res)) *)
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
      //let newv = memread res in
      //let lov = memread lo in
    (*      (multiplesMarkedAsDividesIff n initres newv lo) // how to invoke this lemma now? unlike previously, we cannot read a full Seq from an array
    *)

type markedIffHasDivisorSmallerThan (n:nat) (lo:nat)
    (neww: bitv n) =
    (forall (k:nat{k < n}). (marked n neww k <==> (exists (d:nat{1<d}). d<lo /\ SieveFun.nonTrivialDivides d k)))


val markedIffHasDivisorSmallerThanInc :
  n:nat -> lo:nat{1<lo} -> old:(erased (bitv n)) -> neww:(erased (bitv n))
  -> Lemma
      (requires (markedIffHasDivisorSmallerThan n lo (reveal old))
              /\ markedIffDividesOrInit2 n lo (reveal old) (reveal neww))
      (ensures (markedIffHasDivisorSmallerThan n (lo+1) (reveal neww)))
      (*[SMTPatT (markedIffHasDivisorSmallerThan n (lo+1) neww)]*)
let markedIffHasDivisorSmallerThanInc n lo old neww  = ((multiplesMarkedAsDividesIff n old neww lo))

type allUnmarked
   (n:nat) (neww: bitv n) =
   forall (m:nat{m<n}). not (marked n neww m)

type  outerLoopInv (n:nat) (lo: ref nat) (res: bitarray) (m:smem) =
 SieveFun.distinctRefsExists2 m lo (reveal (asRef res))
  /\ (((loopkupRef lo m) - 1) < n)
  /\ (1<(loopkupRef lo m)) /\  haslength m res n
  /\ (markedIffHasDivisorSmallerThan n (loopkupRef lo m) (reveal (esel m res)))


(*#set-options "--initial_fuel 100 --max_fuel 10000 --initial_ifuel 100 --max_ifuel 10000"*)

(*Danger!! this function is highly experimental*)
assume val memreadAll : unit -> PureMem (erased smem)
      (requires (fun m -> true))
      (ensures (fun _ v m -> reveal v = m))


val outerLoopBody :
  n:nat{n>1}
  -> lo:(ref nat)
  -> res : bitarray
  -> unit ->
  whileBody
    (outerLoopInv n lo res)
    (SieveFun.outerGuardLC n lo)
    ((elift2 union) (gonly lo)  (ArrayAlgos.eonly res))


let outerLoopBody n lo res u =
  let initMem = memreadAll () in
  let lov = memread lo in
  let li = salloc 2 in
  let liv = memread li in
  innerLoop n lo li res (eesel initMem res);
  let fMem = memreadAll () in
  memwrite lo (lov+1);
  (*the part below has no computational content*)
  (markedIffHasDivisorSmallerThanInc n lov (eesel initMem res) (eesel initMem res))

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

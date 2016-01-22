(*--build-config
    other-files:FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.List.fst  stack.fst listset.fst
    FStar.Ghost.fst located.fst lref.fst stackAndHeap.fst sst.fst rstWhile.fst seq.fsi FStar.Seq.fst array.fsi array.fst arrayalgos.fst sieveFun.fst
  --*)
module Sieve
open FStar.Regions.RSTWhile
open StackAndHeap
open FStar.Regions.RST

open Heap
open FStar.Regions.Heap  open FStar.Regions.Located
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
open FStar.Regions.RSTArray

type bitarray = sstarray bool

open FStar.Regions.RSTArray

(* val mark : n:nat -> ((k:nat{k<n}) -> Tot bool) -> index:nat{index<n} -> Tot ((k:nat{k<n}) -> Tot bool) *)
let mark f index =
  writeIndex f index true


type bitv n = b:(Seq.seq bool){Seq.length b =n}

val marked : n:nat -> b:(bitv n) -> m:nat{m<n} -> Tot bool
let marked n f m = (Seq.index f m)


type markedIffMultipleOrInit (n:nat) (lo:nat) (upto:nat)
  (init:bitv n) (neww:bitv n) =
  (forall (k:nat{k < upto /\ 1<k /\ lo*k<n}). marked n neww (lo*k))
  /\ (forall (m:nat{m < n}). (marked n init m ==> marked n neww m))
  /\ (forall (m:nat{m < n}). (marked n neww m ==> (marked n init m \/
      SieveFun.nonTrivialDivides lo m) ))

type  innerLoopInv (n:nat) (lo: lref nat)  (li : lref nat) (res: bitarray)
    (initres: erased (bitv n)) (m:smem) =
 SieveFun.distinctRefsExists3 m lo (reveal (asRef res)) li
  /\ 1 < (lookupRef li m) /\  haslength m res n
   /\ markedIffMultipleOrInit n (lookupRef lo m) (lookupRef li m) (reveal initres) (reveal (esel m res))


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
 /\ lookupRef res m = markMultiplesUpto n lov (lookupRef li m) initres*)

       (*(k < (lookupRef li m))
           ==> (marked n (lookupRef res m) ((lookupRef lo m)*k)))*)

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
  -> lo: lref nat
  -> li : lref nat
  -> res : bitarray
  -> initres : (erased (bitv n))
  -> Mem unit
      (requires (fun m -> innerLoopInv n lo li res initres m /\
        haslength m res n /\
        lookupRef li m = 2  /\ 1 < (lookupRef lo m)
                    /\ reveal (esel m res)  = reveal initres ))
      (ensures (fun _ _ m -> SieveFun.distinctRefsExists3 m lo (reveal (asRef res)) li
                /\ haslength m res n
                /\ markedIffDividesOrInit2 n (lookupRef lo m) (reveal initres) (reveal (esel m res))
                (* markedIffDividesOrInit n (lookupRef lo m) initres (reveal (esel m res)) *)
      ))
      (eunion (only li)  (ArrayAlgos.eonly res))

let innerLoop n lo li res initres =
  (unscopedWhile
    (innerLoopInv n lo li res initres)
    (SieveFun.innerGuardLC n lo li)
    (fun u -> (memread li * memread lo < n))
      (eunion (only li)  (ArrayAlgos.eonly res))
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
    (forall (k:nat{k < n}).
      (marked n neww k <==> (exists (d:nat{1<d}). d<lo /\ SieveFun.nonTrivialDivides d k) ))


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

type  outerLoopInv (n:nat) (li: lref nat) (lo: lref nat) (res: bitarray) (m:smem) =
 SieveFun.distinctRefsExists3 m li lo (reveal (asRef res))
  /\ (((lookupRef lo m) - 1) < n)
  /\ (1<(lookupRef lo m)) /\  haslength m res n
  /\ (markedIffHasDivisorSmallerThan n (lookupRef lo m) (reveal (esel m res)))


(*#set-options "--initial_fuel 100 --max_fuel 10000 --initial_ifuel 100 --max_ifuel 10000"*)


(*Danger!! this function is highly experimental*)


val outerLoopBody :
  n:nat{n>1}
  -> li:(lref nat)
  -> lo:(lref nat)
  -> res : bitarray
  -> unit ->
  whileBodyUnscoped
    (outerLoopInv n li lo res)
    (SieveFun.outerGuardLC n lo)
    (eunion (only li) ((eunion (only lo)  (ArrayAlgos.eonly res))))

let outerLoopBody n li lo res u =
  let initMem : erased smem  = get () in
  let lov = memread lo in
  (memwrite li 2);
  innerLoop n lo li res (eeseln n initMem res);
  memwrite lo (lov+1);
  let fMem : erased smem = get () in
  (*the part below has no computational content*)
  (markedIffHasDivisorSmallerThanInc n lov (eeseln n initMem res) (eeseln n fMem res))

val outerLoop : n:nat{n>1}
  -> li: lref nat
  -> lo: lref nat
  -> res : bitarray
  -> Mem unit
      (fun m -> outerLoopInv n li lo res m /\ lookupRef lo m =2 /\ allUnmarked n (sel m res))
      (fun _ _ m1 -> outerLoopInv n li lo res m1 /\ lookupRef lo m1 = n
        /\ markedIffHasDivisorSmallerThan n n (sel m1 res)
      )
      (eunion (only li) ((eunion (only lo)  (ArrayAlgos.eonly res))))

let outerLoop n li lo res =
  unscopedWhile
    (outerLoopInv n li lo res)
    (SieveFun.outerGuardLC n lo)
    (fun u -> (memread lo < n))
    (eunion (only li) ((eunion (only lo)  (ArrayAlgos.eonly res))))
    (outerLoopBody n li lo res)

(*to work around type inference issues*)
val nmem : nat -> list nat -> Tot bool
let nmem n l = memT n l

val listOfUnmarkedAux : n:nat -> max:nat{max<=n} -> f:bitarray
  -> PureMem (list nat)
        (requires (fun m -> haslength m f n))
        (ensures (fun m l -> haslength m f n /\ (forall (k:nat). (nmem k l) <==> (k<max /\ not (marked n (sel m f) k) ) ) ))

let rec listOfUnmarkedAux n max f = if (max=0) then [] else
  ( if (not (readIndex f (max-1))) then ((max-1)::(listOfUnmarkedAux n (max - 1) f)) else (listOfUnmarkedAux n (max - 1) f))

val listOfUnmarked : n:nat  -> f:bitarray
-> PureMem (list nat)
      (requires (fun m -> haslength m f n))
      (ensures (fun m l -> haslength m f n /\ (forall (k:nat). (nmem k l) <==> (k<n /\ not (marked n (sel m f) k) ) ) ))
let listOfUnmarked n f = listOfUnmarkedAux n n f

val sieve : n:nat{n>1} -> unit
  -> WNSC (list nat)
        (requires (fun m -> True))
        (ensures (fun _ l m -> forall (k:nat). (nmem k l) <==> ((k<n) /\ (~ (exists (d:nat{1<d}). d<n /\ SieveFun.nonTrivialDivides d k))) ))
        //  markedIffHasDivisorSmallerThan n n (sel m resv)))
        (hide empty)

let sieve n u =
  let li = ralloc 2 in
  let lo = ralloc 2 in
  let res = screate n false in
  (outerLoop n li lo res);
  (listOfUnmarked n res)


val sieveFull : n:nat{n>1}
  -> Mem (list nat)
  (requires (fun m -> True))
  (ensures (fun _ l m -> forall (k:nat). (nmem k l) <==> ((k<n) /\ (~ (exists (d:nat{1<d}). d<n /\ SieveFun.nonTrivialDivides d k))) ))
        (hide empty)
let sieveFull n =
  pushRegion ();
  let res= sieve n () in
  popRegion (); res

  val maxUnmarkedAux : n:nat -> max:nat{max<=n} -> f:bitarray
    -> PureMem (nat)
          (requires (fun m -> haslength m f n))
          (ensures (fun m l -> True ))

  let rec maxUnmarkedAux n max f = if (max=0) then 0 else
    ( if (not (readIndex f (max-1))) then (max-1) else (maxUnmarkedAux n (max - 1) f))

  val maxUnmarked : n:nat  -> f:bitarray
  -> PureMem nat
        (requires (fun m -> haslength m f n))
        (ensures (fun m l ->True  ))
  let maxUnmarked n f = maxUnmarkedAux n n f



val sieveJustMax : n:nat{n>1}
  -> Mem nat
  (requires (fun m -> True))
  (ensures (fun _ l m -> True ))
        (hide empty)
let sieveJustMax n =
  pushRegion ();
  let li = ralloc 2 in
  let lo = ralloc 2 in
  let res = screate n false in
  (outerLoop n li lo res);
  let res = (maxUnmarked n res) in
  popRegion (); res

val segFault : unit -> FStar.Regions.RST int (requires (fun _-> True)) (ensures (fun _ _ _ -> True))
let segFault u =
  pushRegion ();
  let p : (int * int) =  (1 , 2) in
  let arr = screate 2 p in
  writeIndex arr 0 (2,3);
  let arr1 = readIndex arr 1 in
  popRegion ();
  (fst arr1) // this neither segfaults, nor prints 2. It prints 1!

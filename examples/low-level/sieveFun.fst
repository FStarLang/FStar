(*--build-config
    other-files:ext.fst set.fsi set.fst heap.fst st.fst all.fst list.fst  stack.fst listset.fst
    ghost.fst located.fst lref.fst stackAndHeap.fst sst.fst sstCombinators.fst
  --*)

module SieveFun
open RSTCombinators
open StackAndHeap
open RST
open Heap
open Lref  open Located
open Stack
open Set
open Prims
open List
open ListSet
open Ghost
(*val divides : pos -> nat -> Tot bool
let divides divisor n = ((n % divisor) = 0)*)
(*Instead, below is a definition from first principles*)


opaque type divides  (divisor :nat) (n:nat) =
exists (k:nat). k*divisor=n

opaque type nonTrivialDivides  (divisor :nat) (n:nat) =
exists (k:nat). k*divisor=n /\ 1<k

type isNotPrime n =
  exists (d:nat). divides d n /\ 1<d /\ d<n

type innerGuardLC (n:nat) (lo : lref nat) (li : lref nat)
(m:smem) =
  (liveRef li m) && (liveRef lo m) &&
    (((loopkupRef li m) * (loopkupRef lo m) < n))

type vector (a:Type) (n:nat) = (k:nat{k<n}) -> Tot a

(*cannot make n implcit, because the typechecker usually canNOT figure it out from f*)
val marked : n:nat -> (vector bool n) -> m:nat{m<n} -> Tot bool
let marked n f m = (f m)


(*li is the counter for the inner loop; lo is for the outer one*)
(*the inner loop invariant says that cells lo*2, lo*3, lo*4 ....lo*(li-1) (first li non-trivial multiples of lo) are marked.*)

(*#set-options "--initial_fuel 100 --max_fuel 100 --initial_ifuel 100 --max_ifuel 100"*)

val mark : n:nat -> ((k:nat{k<n}) -> Tot bool) -> index:nat{index<n} -> Tot ((k:nat{k<n}) -> Tot bool)
let mark n f index =
  (fun indx -> if (indx= index) then true else f indx)

(*using hetrogeneous lists, one can extend this to the general (n-ary) case*)
(*previosly, mtail was need; verify*)
type distinctRefsExists3
  (#a:Type) (#b:Type) (#c:Type) (m:smem)
  (ra:lref a) (rb: lref b) (rc: lref c)  =
  (liveRef ra (m)) /\ (liveRef rb (m)) /\ (liveRef rc m)
  /\ (ra=!=rb) /\ (rb=!=rc) /\ (ra=!=rc)

type markedIffMultipleOrInit (n:nat) (lo:nat) (upto:nat)
  (init:((k:nat{k<n}) -> Tot bool)) (neww:((k:nat{k<n}) -> Tot bool)) =
  (forall (k:nat{k < upto /\ 1<k /\ lo*k<n}). marked n neww (lo*k))
  /\ (forall (m:nat{m < n}). (marked n init m ==> marked n neww m))
  /\ (forall (m:nat{m < n}). (marked n neww m ==> (marked n init m \/
       nonTrivialDivides lo m) ))



type markedIffDividesOrInit2 (n:nat) (lo:nat)
  (init:((k:nat{k<n}) -> Tot bool)) (newres:((k:nat{k<n}) -> Tot bool)) =
  (forall (k:nat{k * lo < n /\ 1<k}). marked n newres (lo*k))
  /\ (forall (m:nat{m < n}). (marked n init m ==> marked n newres m))
  /\ (forall (m:nat{m < n}). (marked n newres m ==> (marked n init m \/
        nonTrivialDivides lo m
    )))


type markedIffDividesOrInit (n:nat) (lo:nat)
   (init:((k:nat{k<n}) -> Tot bool)) (neww:((k:nat{k<n}) -> Tot bool)) =
    (forall (k:nat{k < n}). (marked n neww k <==> (marked n init k \/ nonTrivialDivides lo k)))


type multiplesMarked (n:nat) (bitv : (k:nat{k<n}) -> Tot bool) (lo:nat) =
  (forall (m:nat{m<n}). (nonTrivialDivides lo m) ==> marked n bitv m)
  (* this works, is totally precise, but is hard to use
  /\ loopkupRef res m = markMultiplesUpto n lov (loopkupRef li m) initres*)

        (*(k < (loopkupRef li m))
            ==> (marked n (loopkupRef res m) ((loopkupRef lo m)*k)))*)

type multiplesMarked2 (n:nat) (bitv : (k:nat{k<n}) -> Tot bool) (lo:nat) =
  (forall (k:nat). (k * lo < n /\ 1<k)  ==> marked n bitv (lo*k))

val multiplesMarkedAsDivides :
  n:nat -> bitv:((k:nat{k<n}) -> Tot bool) -> lo:pos
  -> Lemma
    (requires (multiplesMarked2 n bitv lo))
    (ensures (multiplesMarked n bitv lo))
let multiplesMarkedAsDivides n bitv lo = ()


val multiplesMarkedAsDividesIff :
  n:nat -> initv:((k:nat{k<n}) -> Tot bool) -> newv:((k:nat{k<n}) -> Tot bool) -> lo:pos
  -> Lemma
    (requires (markedIffDividesOrInit2 n lo initv newv))
    (ensures (markedIffDividesOrInit n lo initv newv))
    (*[SMTPatT (markedIffDividesOrInit2 n lo initv newv)]*)
let multiplesMarkedAsDividesIff n bitv newv lo = (multiplesMarkedAsDivides n newv lo)

type  innerLoopInv (n:nat) (lo: lref nat)  (li : lref nat) (res:lref ((k:nat{k<n}) -> Tot bool))
    (initres: ((k:nat{k<n}) -> Tot bool)) (m:smem) =
 distinctRefsExists3 m lo res li
  /\ 1 < (loopkupRef li m)
  /\ markedIffMultipleOrInit n (loopkupRef lo m) (loopkupRef li m) initres (loopkupRef res m)

val innerLoop : n:nat{n>1}
  -> lo: lref nat
  -> li : lref nat
  -> res : lref ((k:nat{k<n}) -> Tot bool)
  -> initres : ((k:nat{k<n}) -> Tot bool)
  -> Mem unit
      (requires (fun m -> innerLoopInv n lo li res initres m/\
        (*(liveRef li m) /\ (liveRef lo m) /\ (liveRef res m) /\ (li=!=lo) /\ (lo=!=res) /\ (li=!=res)*)
        loopkupRef li m = 2  /\ 1 < (loopkupRef lo m)
                    /\ loopkupRef res m= initres))
      (ensures (fun _ _ m -> distinctRefsExists3 m lo res li
                /\ markedIffDividesOrInit n (loopkupRef lo m) initres (loopkupRef res m)
      ))
      (hide (union (singleton (Ref li)) (singleton (Ref res))))

let innerLoop n lo li res initres =
  (scopedWhile
    (innerLoopInv n lo li res initres)
    (innerGuardLC n lo li)
    (fun u -> (memread li * memread lo < n))
    (hide (union (singleton (Ref li)) (singleton (Ref res))))
    (fun u ->
      let liv = memread li in
      let lov = memread lo in
      let resv = memread res in
      memwrite li (liv+1);
      memwrite res (mark n resv (lov * liv))));
    (*the part below has no computaional content; why does SMTPatT not work?*)
      let newv = memread res in
      let lov = memread lo in
      (multiplesMarkedAsDividesIff n initres newv lov)

type distinctRefsExists2
  (#a:Type) (#b:Type) (m:smem)
  (ra:lref a) (rb: lref b)  =
  (liveRef ra m) /\ (liveRef rb m)  /\ (ra=!=rb)

type outerGuardLC (n:nat) (lo : lref nat) (m:smem) =
  (liveRef lo m) && ((loopkupRef lo m) < n)

type markedIffHasDivisorSmallerThan (n:nat) (lo:nat)
    (neww:((k:nat{k<n}) -> Tot bool)) =
    (forall (k:nat{k < n}). (marked n neww k <==> (exists (d:nat{1<d}). d<lo /\ nonTrivialDivides d k)))


val markedIffHasDivisorSmallerThanInc :
  n:nat -> lo:nat{1<lo} -> old:((k:nat{k<n}) -> Tot bool) -> neww:((k:nat{k<n}) -> Tot bool)
  -> Lemma
      (requires (markedIffHasDivisorSmallerThan n lo old)
              /\ markedIffDividesOrInit n lo old neww)
      (ensures (markedIffHasDivisorSmallerThan n (lo+1) neww))
      (*[SMTPatT (markedIffHasDivisorSmallerThan n (lo+1) neww)]*)
let markedIffHasDivisorSmallerThanInc n lo old neww  = ()

type allUnmarked
   (n:nat) (neww:((k:nat{k<n}) -> Tot bool)) =
   forall (m:nat{m<n}). not (marked n neww m)


val markedIffHasDivisorSmallerThan2 :
 n:nat -> neww:((k:nat{k<n}) -> Tot bool)
 -> Lemma
     (requires (allUnmarked n neww))
     (ensures (markedIffHasDivisorSmallerThan n 2 neww))
let markedIffHasDivisorSmallerThan2 n neww = ()


type  outerLoopInv (n:nat) (lo: lref nat) (res:lref ((k:nat{k<n}) -> Tot bool)) (m:smem) =
 distinctRefsExists2 m lo res
  /\ (((loopkupRef lo m) - 1) < n)
  /\ (1<(loopkupRef lo m))
  /\ (markedIffHasDivisorSmallerThan n (loopkupRef lo m) (loopkupRef res m))


(*#set-options "--initial_fuel 100 --max_fuel 10000 --initial_ifuel 100 --max_ifuel 10000"*)

val outerLoopBody :
  n:nat{n>1}
  -> lo:(lref nat)
  -> res : lref ((k:nat{k<n}) -> Tot bool)
  -> unit ->
  whileBody
    (outerLoopInv n lo res)
    (outerGuardLC n lo)
    (hide (union (singleton (Ref lo)) (singleton (Ref res))))


let outerLoopBody n lo res u =
  (*pushRegion ();*)
  let initres = memread res in
  let lov = memread lo in
  let li = ralloc 2 in
  let liv = memread li in
  innerLoop n lo li res initres;
  let newres = memread res in
  memwrite lo (lov+1);
  (*the part below has no computational content*)
  (markedIffHasDivisorSmallerThanInc n lov initres newres)

val outerLoop : n:nat{n>1}
  -> lo: lref nat
  -> res : lref ((k:nat{k<n}) -> Tot bool)
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

type markedIffNotPrime
   (n:nat) (neww:((k:nat{k<n}) -> Tot bool)) =
   (forall (m:nat{m<n}). (marked n neww m <==>  ((isNotPrime m))))


(*
val markedIffHasDivisorSmallerThan3 :
n:nat -> neww:((k:nat{k<n}) -> Tot bool)
-> Lemma
    (requires (markedIffHasDivisorSmallerThan n n neww))
    (ensures (markedIffNotPrime n neww))
let markedIffHasDivisorSmallerThan3 n neww = ()
*)

val sieve : n:nat{n>1} -> unit
  -> WNSC ((k:nat{k<n}) -> Tot bool)
        (requires (fun m -> True))
        (ensures (fun _ resv _ -> markedIffHasDivisorSmallerThan n n resv))
        (hide empty)
let sieve n u =
  let lo = ralloc 2 in
  let f:((k:nat{k<n}) -> Tot bool) = (fun x -> false) in
  let res = ralloc f in
  (outerLoop n lo res);
  //assert (False);
  memread res

val sieveFull : n:nat{n>1}
  -> Mem ((k:nat{k<n}) -> Tot bool)
        (requires (fun m -> True))
        (ensures (fun _ resv _ -> markedIffHasDivisorSmallerThan n n resv))
        (hide empty)
let sieveFull n =
  pushRegion ();
  let res= sieve n () in
  popRegion (); res

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

val sieveUnfolded : n:nat{n>1} -> unit
  -> WNSC ((k:nat{k<n}) -> Tot bool)
        (requires (fun m -> True))
        (ensures (fun _ resv _ -> markedIffHasDivisorSmallerThan n n resv))
        (hide empty)
let sieveUnfolded n u =
  let lo = ralloc 2 in
  let f:((k:nat{k<n}) -> Tot bool) = (fun x -> false) in
  let res = ralloc f in
  scopedWhile
    (outerLoopInv n lo res)
    (outerGuardLC n lo)
    (fun u -> (memread lo < n))
    (hide (union (singleton (Ref lo)) (singleton (Ref res))))
    (fun u ->
        let initres = memread res in
        let lov = memread lo in
        let li = ralloc 2 in
        let liv = memread li in
        innerLoop n lo li res initres;
        let newres = memread res in
        memwrite lo (lov+1);
    (*the part below has no computational content*)
      (markedIffHasDivisorSmallerThanInc n lov initres newres));
  memread res


type  innerLoopInv2 (n:nat) (lo: lref nat) (li : lref nat) (res:lref ((k:nat{k<n}) -> Tot bool))
    (initres: ((k:nat{k<n}) -> Tot bool)) (m:smem) =
  (liveRef li m) /\ (liveRef lo m) /\ (liveRef res m)
  /\ ((loopkupRef li m)-1)*(loopkupRef lo m) < n
  /\ markedIffMultipleOrInit n (loopkupRef lo m) (loopkupRef li m) initres (loopkupRef res m)

type  outerLoopInv2 (n:nat) (lo: lref nat) (res:lref ((k:nat{k<n}) -> Tot bool)) (m:smem) =
  liveRef lo m /\ liveRef res m
  /\ (((loopkupRef lo m) - 1) < n)
  /\ (1<(loopkupRef lo m))
  /\ (markedIffHasDivisorSmallerThan n (loopkupRef lo m) (loopkupRef res m))

(*
val sieveUnfolded3 : n:nat{n>1} -> unit
  -> WNSC ((k:nat{k<n}) -> Tot bool)
        (requires (fun m -> True))
        (ensures (fun _ resv _ -> markedIffHasDivisorSmallerThan n n resv))
        empty
let sieveUnfolded3 n u =
  let lo:(lref nat) = ralloc 2 in
  let f:((k:nat{k<n}) -> Tot bool) = (fun x -> false) in
  let res = ralloc f in
  scopedWhile1
    lo
    (fun lov -> lov < n)
    (outerLoopInv2 n lo res)
    (union (singleton (Ref lo)) (singleton (Ref res)))
    (fun u ->
        let initres = memread res in
        let lov = memread lo in
        let li:(lref nat) = ralloc 2 in
        let liv = memread li in
        (scopedWhile2
            lo
            li
            (fun lov liv -> liv *lov < n)
            (innerLoopInv2 n lo li res initres)
            (union (singleton (Ref li)) (singleton (Ref res)))
            (fun u ->
              let liv = memread li in
              let lov = memread lo in
              let resv = memread res in
              memwrite li (liv+1);
              memwrite res (mark n resv (lov * liv))));

          (*the part below has no computaional content; why does SMTPatT not work?*)
        let newv = memread res in
        (multiplesMarkedAsDividesIff n initres newv lov);
        let newres = memread res in
        memwrite lo (lov+1);
    (*the part below has no computational content*)
      (markedIffHasDivisorSmallerThanInc n lov initres newres));
  memread res


val sieveUnfolded2 : n:nat{n>1} -> unit
  -> WNSC ((k:nat{k<n}) -> Tot bool)
        (requires (fun m -> True))
        (ensures (fun _ resv _ -> markedIffHasDivisorSmallerThan n n resv))
        empty
let sieveUnfolded2 n u =
  let lo = ralloc 2 in
  let f:((k:nat{k<n}) -> Tot bool) = (fun x -> false) in
  let res = ralloc f in
  scopedWhile
    (outerLoopInv2 n lo res)
    (outerGuardLC n lo)
    (fun u -> (memread lo < n))
    (union (singleton (Ref lo)) (singleton (Ref res)))
    (fun u ->
        let initres = memread res in
        let lov = memread lo in
        let li = ralloc 2 in
        let liv = memread li in
        (scopedWhile
            (innerLoopInv2 n lo li res initres)
            (innerGuardLC n lo li)
            (fun u -> (memread li * memread lo < n))
            (union (singleton (Ref li)) (singleton (Ref res)))
            (fun u ->
              let liv = memread li in
              let lov = memread lo in
              let resv = memread res in
              memwrite li (liv+1);
              memwrite res (mark n resv (lov * liv))));

          (*the part below has no computaional content; why does SMTPatT not work?*)
        let newv = memread res in
        (multiplesMarkedAsDividesIff n initres newv lov);
        let newres = memread res in
        memwrite lo (lov+1);
    (*the part below has no computational content*)
      (markedIffHasDivisorSmallerThanInc n lov initres newres));
  memread res
*)

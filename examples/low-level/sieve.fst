(*--build-config
    options:--admit_fsi Set --z3timeout 10;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst  stack.fst listset.fst st3.fst $LIB/constr.fst
  --*)

module ScopedWhile3
open StructuredMem
open Heap
open Stack
open Set
open Prims
open List
open ListSet
open Constructive



(*val divides : pos -> nat -> Tot bool
let divides divisor n = ((n % divisor) = 0)*)
(*Instead, below is a definition from first principles*)

opaque type divides  (divisor :nat) (n:nat) =
exists (k:nat). k*divisor=n
(*cexists (fun (k:nat) -> b2t (k*divisor=n))*)
(*switching to cexists breaks many lemmas.
 I guess the SMT solver does not know anything about cexists.*)

val divisorSmall : n:nat{1<n} -> divisor:nat
  ->
   Lemma
       ( requires (divides divisor n /\ 1<divisor))
       (ensures (divisor < n))
       [SMTPatT (divides divisor n)]
let divisorSmall n divisor = (admit ())


 val isNotPrimeIf2 :
   n:nat{1<n} -> m:nat{1<m /\ m<n}
   -> Lemma
   (requires (exists (d:nat{1<d}). d<n /\ divides d m))
   (ensures (exists (d:nat{1<d}).{:pattern (divides d m)} d<m /\ divides d m))

 let isNotPrimeIf2 n m = ()


type isNotPrime n =
exists (d:nat). (1<d /\ d<n /\ (divides d n))
(*cexists (fun (d:nat) -> (1<d /\ d<n /\ (divides d n)))*)

(*this program has nested loops. first, we define the inner loop*)
(*The program will be asked to compute first n primes. *)
(*Suppose we are at the m^th iteration in the outer loop*)

type innerGuardLC (n:nat) (lo : ref nat) (li : ref nat)
(m:smem) =
  (refExistsInMem li m) && (refExistsInMem lo m) &&
    (((loopkupRef li m) * (loopkupRef lo m) < n))

type vector (a:Type) (n:nat) = (k:nat{k<n}) -> Tot a

(*cannot make n implcit, because the typechecker usually canNOT figure it out from f*)
val marked : n:nat -> (vector bool n) -> m:nat{m<n} -> Tot bool
let marked n f m = (f m)

(*#set-options "--initial_fuel 100 --max_fuel 10000 --initial_ifuel 100 --max_ifuel 10000"*)
(*delta-folding vector creates a wierd error; see below*)

(*li is the counter for the inner loop; lo is for the outer one*)
(*the inner loop invariant says that cells lo*0, lo*1, lo*2 ....lo*(li-1) (first li multiples of lo) are marked.*)

(*#set-options "--initial_fuel 100 --max_fuel 100 --initial_ifuel 100 --max_ifuel 100"*)

val mark : n:nat -> ((k:nat{k<n}) -> Tot bool) -> index:nat{index<n} -> Tot ((k:nat{k<n}) -> Tot bool)
let mark n f index =
  (fun indx -> if (indx= index) then true else f indx)

(*using hetrogeneous lists, one can extend this to the general (n-ary) case*)
(*previosly, mtail was need; verify*)
type distinctRefsExists3
  (#a:Type) (#b:Type) (#c:Type) (m:smem)
  (ra:ref a) (rb: ref b) (rc: ref c)  =
  (refExistsInMem ra (m)) /\ (refExistsInMem rb (m)) /\ (refExistsInMem rc m)
  /\ (ra=!=rb) /\ (rb=!=rc) /\ (ra=!=rc)

val markMultiplesUpto : n:nat -> lo:nat -> upto:nat{lo*(upto-1)<n}
  ->((k:nat{k<n}) -> Tot bool) -> Tot ((k:nat{k<n}) -> Tot bool)
let rec markMultiplesUpto n lo upto f =
match upto with
| 0 -> f
| _ -> (mark n (markMultiplesUpto n lo (upto-1) f) ((upto-1)*lo))
(* in below, markings are done in a reverse order as that of the while loop
| _ -> markMultiplesUpto n lo (upto-1) (mark n f ((upto-1)*lo))*)

type markedIffMultipleOrInit (n:nat) (lo:nat) (upto:nat{lo*(upto-1)<n})
  (init:((k:nat{k<n}) -> Tot bool)) (new:((k:nat{k<n}) -> Tot bool)) =
  (forall (k:nat{k < upto}). marked n new (lo*k))
  /\ (forall (k:nat{k < n}). (marked n init k ==> marked n new k))
  /\ (forall (k:nat{k < n}). (marked n new k ==> (marked n init k \/ divides lo k)))

type  innerLoopInv (n:nat) (lo: ref nat) (lov:nat) (li : ref nat) (res:ref ((k:nat{k<n}) -> Tot bool))
    (initres: ((k:nat{k<n}) -> Tot bool)) (m:smem) =
 distinctRefsExists3 m lo res li
  /\ loopkupRef lo m = lov
  /\ ((loopkupRef li m)-1)*lov < n
  /\ markedIffMultipleOrInit n lov (loopkupRef li m) initres (loopkupRef res m)

  (* this works, is totally precise, but is hard to use
  /\ loopkupRef res m = markMultiplesUpto n lov (loopkupRef li m) initres*)

        (*(k < (loopkupRef li m))
            ==> (marked n (loopkupRef res m) ((loopkupRef lo m)*k)))*)

type multiplesMarked2 (n:nat) (bitv : (k:nat{k<n}) -> Tot bool) (lo:nat) =
(forall (k:nat). (k * lo < n)  ==> marked n bitv (lo*k))


type markedIffDividesOrInit2 (n:nat) (lo:nat)
  (init:((k:nat{k<n}) -> Tot bool)) (new:((k:nat{k<n}) -> Tot bool)) =
  (forall (k:nat{k * lo < n}). marked n new (lo*k))
  /\ (forall (k:nat{k < n}). (marked n init k ==> marked n new k))
  /\ (forall (k:nat{k < n}). (marked n new k ==> (marked n init k \/ divides lo k)))


type markedIffDividesOrInit (n:nat) (lo:nat)
   (init:((k:nat{k<n}) -> Tot bool)) (new:((k:nat{k<n}) -> Tot bool)) =
    (forall (k:nat{k < n}). (marked n new k <==> (marked n init k \/ divides lo k)))

type multiplesMarked (n:nat) (bitv : (k:nat{k<n}) -> Tot bool) (lo:nat) =
(forall (m:nat{m<n}). (divides lo m) ==> marked n bitv m)

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

val innerLoop : n:nat{n>1}
  -> lo: ref nat
  -> lov:nat
  -> li : ref nat
  -> res : ref ((k:nat{k<n}) -> Tot bool)
  -> initres : ((k:nat{k<n}) -> Tot bool)
  -> SSST unit
      (requires (fun m ->
        (*(refExistsInMem li m) /\ (refExistsInMem lo m) /\ (refExistsInMem res m) /\ (li=!=lo) /\ (lo=!=res) /\ (li=!=res)*)
        distinctRefsExists3 m lo res li /\ loopkupRef li m = 0
                    /\ loopkupRef lo m = lov /\ loopkupRef res m= initres))
      (ensures (fun m0 _ m1 -> distinctRefsExists3 m1 lo res li
                      /\ loopkupRef lo m1 = lov
                      /\ markedIffDividesOrInit n (loopkupRef lo m1) initres (loopkupRef res m1)
      ))

let innerLoop n lo lov li res initres =
  (scopedWhile
    (innerLoopInv n lo lov li res initres)
    (innerGuardLC n lo li)
    (fun u -> (memread li * memread lo < n))
    (fun u ->
      let liv = memread li in
      let lov = memread lo in
      let resv = memread res in
      memwrite li (liv+1);
      memwrite res (mark n resv (lov * liv))));

    (*the part below has no computaional content; why does SMTPatT not work?*)
      let newv = memread res in
      (multiplesMarkedAsDividesIff n initres newv lov)

type distinctRefsExists2
  (#a:Type) (#b:Type) (m:smem)
  (ra:ref a) (rb: ref b)  =
  (refExistsInMem ra m) /\ (refExistsInMem rb m)  /\ (ra=!=rb)

type outerGuardLC (n:nat) (lo : ref nat) (m:smem) =
  (refExistsInMem lo m) && ((loopkupRef lo m) < n)


type markedIffHasDivisorSmallerThan (n:nat) (lo:nat)
    (new:((k:nat{k<n}) -> Tot bool)) =
    (forall (k:nat{k < n}). (marked n new k <==> (exists (d:nat{1<d}). d<lo /\ divides d k)))


val markedIffHasDivisorSmallerThanInc :
  n:nat -> lo:nat{1<lo} -> old:((k:nat{k<n}) -> Tot bool) -> new:((k:nat{k<n}) -> Tot bool)
  -> Lemma
      (requires (markedIffHasDivisorSmallerThan n lo old)
              /\ markedIffDividesOrInit n lo old new)
      (ensures (markedIffHasDivisorSmallerThan n (lo+1) new))
      (*[SMTPatT (markedIffHasDivisorSmallerThan n (lo+1) new)]*)
let markedIffHasDivisorSmallerThanInc n lo old new  = ()

type allUnmarked
   (n:nat) (new:((k:nat{k<n}) -> Tot bool)) =
   forall (m:nat{m<n}). not (marked n new m)


val markedIffHasDivisorSmallerThan2 :
 n:nat -> new:((k:nat{k<n}) -> Tot bool)
 -> Lemma
     (requires (allUnmarked n new))
     (ensures (markedIffHasDivisorSmallerThan n 2 new))
let markedIffHasDivisorSmallerThan2 n new = ()


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


let outerLoopBody n lo res u =
  (*pushStackFrame ();*)
  let initres = memread res in
  let lov = memread lo in
  let li = salloc 0 in
  let liv = memread li in
  innerLoop n lo lov li res initres;
  let newres = memread res in
  memwrite lo (lov+1);
  (*the part below has no computational content*)
  (markedIffHasDivisorSmallerThanInc n lov initres newres)

val outerLoop : n:nat{n>1}
  -> lo: ref nat
  -> res : ref ((k:nat{k<n}) -> Tot bool)
  -> SSST unit
      (fun m -> distinctRefsExists2 m lo res /\ loopkupRef lo m =2 /\ allUnmarked n (loopkupRef res m))
      (fun m0 _ m1 ->
            distinctRefsExists2 m1 lo res
            /\ sids m0 = sids m1
           /\ (markedIffHasDivisorSmallerThan n n (loopkupRef res m1))
      )

let outerLoop n lo res =
  scopedWhile
    (outerLoopInv n lo res)
    (outerGuardLC n lo)
    (fun u -> (memread lo < n))
    (outerLoopBody n lo res)

type markedIffNotPrime
   (n:nat) (new:((k:nat{k<n}) -> Tot bool)) =
   (forall (m:nat{m<n}). (marked n new m <==>  ((isNotPrime m))))


val lessTrans : m:nat -> n:nat -> d:nat ->
  Lemma (requires (d<n /\ m <n))
          (ensures (d<n))
let lessTrans n m d = ()


val isNotPrimeIf :
  n:nat -> m:nat{m<n}
  -> Lemma
  ((exists (d:nat{1<d}). d<m /\ divides d m))
  (((isNotPrime m)))
let isNotPrimeIf n m = ()


val existsWeakining : #a:Type
  ->p:(a -> Type) -> q:(a->Type)
  -> Lemma
      (requires ((forall x. p x ==> q x)) /\ (exists y. p y))
      (ensures (exists z. q z))
let existsWeakining 'a 'p 'q = ()

(*is this consistent? of course it breakes canonicity*)
assume val existsCexists : #a:Type
  ->p:(a -> Type)
  ->u:unit{exists x. p x}
  -> cexists p

(*this should work without needing admit*)
val cexistsExists :
#a:Type
  ->p:(a -> Type)
  -> cexists p
  ->u:unit{exists x. p x}
let cexistsExists 'a 'p c =
match c with
| ExIntro x  px -> (admit ())


(*how can one manually provide a witness to an existential? switch to cexists completely?*)

val markedIffHasDivisorSmallerThan3 :
n:nat -> new:((k:nat{k<n}) -> Tot bool)
-> Lemma
    (requires (markedIffHasDivisorSmallerThan n n new))
    (ensures (markedIffNotPrime n new))
(*let markedIffHasDivisorSmallerThan3 n new = ()*)


val sieve : n:nat{n>1} -> unit
  -> WNSC ((k:nat{k<n}) -> Tot bool)
        (requires (fun m -> True))
        (ensures (fun _ resv _ -> markedIffHasDivisorSmallerThan n n resv))
let sieve n u =
  let lo = salloc 2 in
  let f:((k:nat{k<n}) -> Tot bool) = (fun x -> false) in
  let res = salloc f in
  (outerLoop n lo res);
  memread res


val sieveUnfolded : n:nat{n>1} -> unit
  -> WNSC ((k:nat{k<n}) -> Tot bool)
        (requires (fun m -> True))
        (ensures (fun _ resv _ -> markedIffHasDivisorSmallerThan n n resv))
let sieveUnfolded n u =
  let lo = salloc 2 in
  let f:((k:nat{k<n}) -> Tot bool) = (fun x -> false) in
  let res = salloc f in
  scopedWhile
    (outerLoopInv n lo res)
    (outerGuardLC n lo)
    (fun u -> (memread lo < n))
    (fun u ->
        let initres = memread res in
        let lov = memread lo in
        let li = salloc 0 in
        let liv = memread li in
        innerLoop n lo lov li res initres;
        let newres = memread res in
        memwrite lo (lov+1);
    (*the part below has no computational content*)
      (markedIffHasDivisorSmallerThanInc n lov initres newres));
  memread res


type  innerLoopInv2 (n:nat) (lo: ref nat) (lov:nat) (li : ref nat) (res:ref ((k:nat{k<n}) -> Tot bool))
    (initres: ((k:nat{k<n}) -> Tot bool)) (m:smem) =
  (refExistsInMem li m) /\ (refExistsInMem lo m) /\ (refExistsInMem res m)
  /\ loopkupRef lo m = lov
  /\ ((loopkupRef li m)-1)*lov < n
  /\ markedIffMultipleOrInit n lov (loopkupRef li m) initres (loopkupRef res m)

type  outerLoopInv2 (n:nat) (lo: ref nat) (res:ref ((k:nat{k<n}) -> Tot bool)) (m:smem) =
  refExistsInMem lo m /\ refExistsInMem res m
  /\ (((loopkupRef lo m) - 1) < n)
  /\ (1<(loopkupRef lo m))
  /\ (markedIffHasDivisorSmallerThan n (loopkupRef lo m) (loopkupRef res m))


val sieveUnfolded2 : n:nat{n>1} -> unit
  -> WNSC ((k:nat{k<n}) -> Tot bool)
        (requires (fun m -> True))
        (ensures (fun _ resv _ -> markedIffHasDivisorSmallerThan n n resv))
let sieveUnfolded2 n u =
  let lo = salloc 2 in
  let f:((k:nat{k<n}) -> Tot bool) = (fun x -> false) in
  let res = salloc f in
  scopedWhile
    (outerLoopInv2 n lo res)
    (outerGuardLC n lo)
    (fun u -> (memread lo < n))
    (fun u ->
        let initres = memread res in
        let lov = memread lo in
        let li = salloc 0 in
        let liv = memread li in
        (scopedWhile
            (innerLoopInv2 n lo lov li res initres)
            (innerGuardLC n lo li)
            (fun u -> (memread li * memread lo < n))
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

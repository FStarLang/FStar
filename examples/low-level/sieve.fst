(*--build-config
    options:--admit_fsi Set;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst  stack.fst listset.fst st3.fst example1.fst
  --*)

module ScopedWhile3
open StructuredMem
open Heap
open Stack
open Set
open Prims
open List
open ListSet


(*val divides : pos -> nat -> Tot bool
let divides divisor n = ((n % divisor) = 0)*)
(*Instead, below is a definition from first principles*)
type divides  (divisor :nat) (n:nat) = exists (k:nat). k*divisor=n

type isPrime n = forall (m:nat). ((2<m /\ m<n) ==> ~ (divides m n))

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
type distinctRefsExists3
  (#a:Type) (#b:Type) (#c:Type) (m:smem)
  (ra:ref a) (rb: ref b) (rc: ref c)  =
  (refExistsInMem ra (mtail m)) /\ (refExistsInMem rb (mtail m)) /\ (refExistsInMem rc m) /\ (ra=!=rb) /\ (rb=!=rc) /\ (ra=!=rc)

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
let multiplesMarkedAsDividesIff n bitv newv lo = (multiplesMarkedAsDivides n newv lo)


val innerLoop : n:nat{n>1}
  -> lo: ref nat
  -> lov:nat
  -> li : ref nat
  -> res : ref ((k:nat{k<n}) -> Tot bool)
  -> initres : ((k:nat{k<n}) -> Tot bool)
  -> SST unit
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
      (*the part below has no computaional content*)
      let newv = memread res in
      (multiplesMarkedAsDividesIff n initres newv lov)

type distinctRefsExists2
  (#a:Type) (#b:Type) (m:smem)
  (ra:ref a) (rb: ref b)  =
  (refExistsInMem ra m) /\ (refExistsInMem rb m)  /\ (ra=!=rb)

type outerGuardLC (n:nat) (lo : ref nat)
(m:smem) =
  (refExistsInMem lo m) && ((loopkupRef lo m) < n)

type  outerLoopInv (n:nat) (lo: ref nat) (res:ref ((k:nat{k<n}) -> Tot bool)) (m:smem) =
 distinctRefsExists2 m lo res
  /\ (((loopkupRef lo m) - 1) < n)
  /\ (1<(loopkupRef lo m))
  /\ (forall (k:nat).
        (1<k /\ k < (loopkupRef lo m)) ==> markedIffDividesOrInit n k (fun _ -> false) (loopkupRef res m))

(*val ex23 : #a:Type -> #b:Type  -> #c:Type -> m:smem
  -> ra:ref a -> rb: ref b -> rc: ref c
  -> Lemma
        (requires (distinctRefsExists2 m ra rb /\ refExistsInMem rc m /\ (rc=!=ra) /\ (rc=!=rb)))
        (ensures (distinctRefsExists3 m ra rb rc))
let ex23 m ra rb rc = ()

val ex23p : #a:Type -> #b:Type  -> #c:Type
  -> ra:ref a -> rb: ref b -> rc: ref c
  -> Lemma
        (requires (True))
        (ensures  ( forall m.
                    ((distinctRefsExists2 (mtail m) ra rb /\ refExistsInMem rc m /\ (rc=!=ra) /\ (rc=!=rb)))
                    ==> ((distinctRefsExists3 m ra rb rc))))*)

(*let ex23p ra rb rc = ()*)
#set-options "--initial_fuel 100 --max_fuel 10000 --initial_ifuel 100 --max_ifuel 10000"

val factorialLoopBody :
  n:nat{n>1}
  -> lo:(ref nat)
  -> res : ref ((k:nat{k<n}) -> Tot bool)
  -> unit ->
  (*whileBody
  (*SST unit*)
    (fun m ->  distinctRefsExists2 m lo res)
    (*(outerGuardLC n lo)*)
    (fun  _ -> True)
    (*(fun  _ _ _ -> True)*)*)

    (*WNSC unit (fun m -> distinctRefsExists2 m lo res)
                (fun _ _ m1 -> distinctRefsExists2 m1 lo res)*)



                  SST unit
                      ( (*requires *) (fun m -> isNonEmpty (st m) /\ topstb m = emp
                      /\ distinctRefsExists2 (mtail m) lo res
                      ))
                        (*)*)
                      ( (* ensures *) (fun m0 _ m1 -> True
                        /\ distinctRefsExists2 (mtail m1) lo res
                          (*/\ sids m0 = sids m1*)
                          )) (*body popped all and only the stack frames it pushed*)


let factorialLoopBody n lo res u =
  (*pushStackFrame ();*)
  let initres = memread res in
  let lov = memread lo in
  let li = salloc 0 in
  let liv = memread li in
  innerLoop n lo lov li res initres;
  memwrite lo (lov+1)



effect SSTNull = SST unit (fun _ -> True) (fun _ _ _ -> True)


val testSalloc1 : unit -> SST unit (fun _ -> True) (fun _ _ _ -> True)
let testSalloc1 () =
  pushStackFrame ();
  let xi=salloc 0 in
  memwrite xi 1;
  pushStackFrame ();
  memwrite xi 1

val testSalloc2 : xi:ref int -> SST unit (fun m -> b2t (refExistsInMem xi m)) (fun _ _ m1 -> b2t (refExistsInMem xi m1))
let testSalloc2 xi =
  pushStackFrame ();
  memwrite xi 1;
  popStackFrame ();
  memwrite xi 1



  val outerLoop : n:nat{n>1}
    -> lo: ref nat
    -> res : ref ((k:nat{k<n}) -> Tot bool)
    -> SST unit
        (fun m -> distinctRefsExists2 m lo res /\ loopkupRef lo m =2)
        (fun m0 _ m1 ->
              distinctRefsExists2 m1 lo res
             /\ (forall (k:nat).
                  (k < n ==> multiplesMarked n (loopkupRef res m1) k))
        )

(*
let outerLoop n lo res =
  scopedWhile
    (outerLoopInv n lo res)
    (outerGuardLC n lo)
    (fun u -> (memread lo < n))
    (fun u ->
      let li = salloc 0 in
      let resv = memread res in
      let lov = memread lo in
      innerLoop n lo lov li res resv;
      memwrite lo (lov+1)
      )*)

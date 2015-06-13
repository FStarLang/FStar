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


val divides : pos -> nat -> Tot bool
let divides divisor n = ((n % divisor) = 0)

val hasDivisorsSmallerThan : nat -> nat -> Tot bool
let rec hasDivisorsSmallerThan n bnd =
match bnd with
| 0 ->  (assert (9%7=2)); false
| _ -> (divides bnd n) || (hasDivisorsSmallerThan n (bnd-1))

val isPrime2 : nat -> Tot bool
let isPrime2 n = hasDivisorsSmallerThan n n

type isPrime n = forall (m:nat). ((2<m /\ m<n) ==> not (divides m n))

(*this program has nested loops. first, we define the inner loop*)
(*The program will be asked to compute first n primes. *)
(*Suppose we are at the m^th iteration in the outer loop*)

(*in a simplified version both inner and outer guards are same; just different variables*)
type guardLC (n:nat) (li : ref nat) (lo : ref nat)
(m:smem) =
  (refExistsInMem li m) && (refExistsInMem lo m) && (((loopkupRef li m) * (loopkupRef lo m) < n))

val guard :  n:nat -> li:(ref nat) -> lo:(ref nat)  -> unit
  -> whileGuard (fun m ->  (refExistsInMem li m) /\ (refExistsInMem lo m))
                (guardLC n li lo)
let guard n li lo u = (memread li * memread lo < n)
(* the guard of a while loop is not supposed to change the memory*)

type vector (a:Type) (n:nat) = (k:nat{k<n}) -> Tot a

type refBitVector (n:nat) = ref (vector bool n)

(*cannot make n implcit, because the typechecker usually canNOT figure it out from f*)
val marked : n:nat -> (vector bool n) -> m:nat{m<n} -> Tot bool
let marked n f m = (f m)

(*#set-options "--initial_fuel 100 --max_fuel 10000 --initial_ifuel 100 --max_ifuel 10000"*)
(*delta-folding vector creates a wierd error; see below*)

(*nmult, for times when the typechecker confuses nats and ints*)
val nmult : nat -> nat -> Tot nat
let nmult n m = n*m

val bforall : (nat -> Tot bool) -> nat -> Tot bool
let rec bforall f bound =
match bound with
| 0 -> true
| _ -> (f bound) && (bforall f (bound -1))

(*li is the counter for the inner loop; lo is for the outer one*)
(*the inner loop invariant says that cells lo*0, lo*1, lo*2 ....lo*(li-1) (first li multiples of lo) are marked.*)

#set-options "--initial_fuel 100 --max_fuel 1000 --initial_ifuel 100 --max_ifuel 1000"

type  innerLoopInv (n:nat) (lo: ref nat) (li : ref nat) (res:ref ((k:nat{k<n}) -> Tot bool)) (m:smem) =
  (guardLC n li lo m)
  /\ (refExistsInMem res m)
  /\ (forall (k:nat).
        (k < (loopkupRef li m)) ==> (marked n (loopkupRef res m) ((loopkupRef lo m)*k)))

val mark : n:nat -> ((k:nat{k<n}) -> Tot bool) -> index:nat{index<n} -> Tot ((k:nat{k<n}) -> Tot bool)
let mark n f index =
  (fun indx -> if (indx= index) then true else f indx)

(*we are inside a loop, so, we have a fresh stack at each iteration of the loop.
 we store li there. creating li is a part of the outer loop*)

val innerLoop : n:nat
  -> lo: ref nat
  -> li : ref nat
  -> res : ref ((k:nat{k<n}) -> Tot bool)
  -> SST unit (fun m -> refExistsInMem lo m /\ refExistsInMem res m /\ (mreads li 0 m) /\ ~(li=lo))
              (fun _ _ m1 -> refExistsInMem lo m1 /\ refExistsInMem res m1 /\  refExistsInMem li m1
                  /\ (forall (k:nat). (k * (loopkupRef lo m1) < n)  ==> marked n (loopkupRef res m1) ((loopkupRef lo m1)*k))
                  )

(*let innerLoop n lo li res =
  scopedWhile
    (innerLoopInv n lo li res)
    (fun m -> (refExistsInMem li m) /\ ((loopkupRef li m) < n))
    (fun u -> (memread li < n))
    (fun u ->
      let liv = memread li in
      let lov = memread lo in
      let resv = memread res in
      memwrite li (liv+1);
      memwrite res (mark n resv (lov * liv)))*)

      (*let resv2=memread res in
      assert (resv2==resv);*)

(*val innerLoopBody :
  n:nat -> lo:(ref pos) -> li:(ref pos) -> res:(ref (ll:seq bool{length ll=n}))
  -> unit ->
  whileBody (innerLoopInv n li lo res) (guardLC n li)*)

(*--build-config
    options:--admit_fsi Set;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst stack.fst listset.fst st3.fst
  --*)
module Example1
open StructuredMem
open Heap
open Stack
open Set
open Prims
open List
open ListSet


(*a good aspect of the current formulation is that the heap/stack difference
only matters at the time of allocation. Functions like increment can be
defined without without bothering about that distinction*)

(*ideally, the refExistsInMem clauses should not be needed in the postcondition*)
val incrementRef : r:(ref int) -> SST unit  (fun m -> (refExistsInMem r m)==true)
(fun m0 a m1 -> (refExistsInMem r m0) /\ (refExistsInMem r m1) /\ (mstail m0 = mstail m1) /\ (loopkupRef r m1 = (loopkupRef r m0) + 1))
let incrementRef r =
  let oldv = memread r in
  memwrite r (oldv + 1)

val pushPopNoChage : unit ->  SST unit  (fun _ -> True) (fun m0 vo m1 -> m0 == m1)
let pushPopNoChage () =
  pushStackFrame (); (* As expected, removing this line results in an error, even for the trivial postcondition*)
  popStackFrame ()


val incrementUsingStack : vi:int -> SST int  (fun _ -> True)
    (fun m0 vo m1 -> m0 = m1 /\ vo=vi+1)
let incrementUsingStack vi =
  pushStackFrame ();
    let r = salloc vi in
    let oldv = memread r in
    memwrite r (oldv + 1);
    let v = (memread r) in
  popStackFrame ();
  v


val incrementRef2 : r:(ref int) -> SST unit
(fun m -> (refExistsInMem r m)
              /\ (isNonEmpty (st m))
              /\ (refLoc r = InStack (topstid m)))
(fun m0 a m1 -> (refExistsInMem r m0) /\ (refExistsInMem r m1)
    /\ (mtail m0 = mtail m1)
    /\ (loopkupRef r m1 = (loopkupRef r m0) + 1))
let incrementRef2 r =
  let oldv = memread r in
  memwrite r (oldv + 1)

(* an example illustrating a typical C idiom :
  caller allocates memory and passes the ref to callee to get some work done *)
val incrementUsingStack2 : vi:int -> SST int  (fun _ -> True)
    (fun m0 vo m1 -> m0 = m1 /\ vo=vi+1)
let incrementUsingStack2 vi =
  pushStackFrame ();
    let r = salloc vi in
    incrementRef2 r; (*why doesn't incrementRef work here?*)
    let v = (memread r) in
  popStackFrame ();
  v

val incrementUsingStack3 : vi:int -> SST int  (fun _ -> True)
    (fun m0 vo m1 ->  m0 =  m1 /\ vo=vi+1)
let incrementUsingStack3 vi =
  pushStackFrame ();
  pushStackFrame ();
    let r = salloc vi in
    let r2 = salloc 0 in
    let oldv = memread r in
    memwrite r (oldv + 1);
    memwrite r2 2; (*a dummy operation bwteen write r and read r*)
    let v = (memread r) in
  popStackFrame ();
  v

(* Why am I able to write this if then else with effectful computations in the brances?
   What is going on under the hood?
   Is this because of the ite_wp in the definition of an effect? *)
val incrementIfNot2 : r:(ref int) -> SST int  (fun m -> (refExistsInMem r m)==true)
(fun m0 a m1 -> (refExistsInMem r m0) /\ (refExistsInMem r m1) /\ (mstail m0 = mstail m1) /\ True)
let equal2 r =
  let oldv = memread r in
  (if (oldv=2)
    then memwrite r 2
    else memwrite r (oldv + 1));oldv

val factorial : nat -> Tot nat
let rec factorial n =
match n with
| 0 -> 1
| n -> n * factorial (n - 1)


val factorialGuard :  n:nat -> li:(ref nat)  -> unit
  -> whileGuard (fun m -> b2t (refExistsInMem li m))
                (fun m -> (refExistsInMem li m) /\ ((loopkupRef li m) <n))
let factorialGuard n li u = (memread li < n)

(*
Why does the following not work?
let factorialGuard () = true
*)

(* the guard of a while loop is not supposed to change the memory*)

val factorialLoopBody : n:nat -> li:(ref nat) -> res:(ref nat)
  -> whileBody (fun m -> refExistsInMem li m /\ refExistsInMem res m (*/\ loopkupRef res m == factorial (loopkupRef li m) *))
    (fun m -> (refExistsInMem li m) /\ ((loopkupRef li m) <n))
let factorialLoopBody n li res  =
    let liv = memread li in
    memwrite li (liv + 1);
    memwrite res ((memread res) * liv)
(*now, in a new scope, allocate res and li, with initial values 1 and 0 respecctively,
  and then call the body
*)

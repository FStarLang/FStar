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

val helloWorld : unit -> SST unit  (fun m -> True) (fun m0 a m1 -> True)
let helloWorld () = (newStackFrame ())



(*a good aspect of the current formulation is that the heap/stack difference
only matters at the time of allocation. Functions like increment can be
defined without without bothering about that distinction*)
val increment : r:(ref int) -> SST unit  (fun m -> (refExistsInMem r m)==true) (fun m0 a m1 -> True)
let increment r =
  let oldv = read r in
  write r (oldv + 1)

(*ideally, the refExistsInMem clauses should not be needed in the postcondition*)
val increment2 : r:(ref int) -> SST unit  (fun m -> (refExistsInMem r m)==true)
(fun m0 a m1 -> (refExistsInMem r m0) /\ (refExistsInMem r m1) /\ (loopkupRef r m1 = (loopkupRef r m0) + 1))
let increment2 r =
  let oldv = read r in
  write r (oldv + 1)

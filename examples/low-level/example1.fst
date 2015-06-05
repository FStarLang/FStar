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



val increment : (ref int) -> SST unit  (fun m -> True) (fun m0 a m1 -> True)
let increment r = admit ()

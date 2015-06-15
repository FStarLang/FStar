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



type vector (a:Type) (n:nat) = (k:nat{k<n}) -> Tot a


(*type  innerLoopInv (n:nat)  (res:ref (vector bool n))
     (m:smem) =
  refExistsInMem res m
  /\ loopkupRef res m  = loopkupRef res m*)


  type  innerLoopInv (n:nat)  (res:ref ((k:nat{k<n}) -> Tot bool))
       (m:smem) =
    refExistsInMem res m
    /\ loopkupRef res m  = loopkupRef res m

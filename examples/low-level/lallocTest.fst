(*--build-config
    variables:LIB=../../lib;
    variables:MATHS=../maths;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/set.fst $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/list.fst stack.fst listset.fst $LIB/ghost.fst located.fst lref.fst stackAndHeap.fst sst.fst
  --*)

(*perhaps this should be an interface file?*)

module LallocTest
open SST
open StackAndHeap
open Located
open Heap
open Stack
open Set
open Prims
open List
open Lref  open Located
open ListSet



(*see example usages of lalloc and lift in lallocTest.fst*)
type point = {x:int ; y:int}

val lx : p:(located point) -> PureMem int (requires (fun m-> liveLoc p m))
              (ensures (fun v m1 -> v == (greveal p).x ))
let lx p =  (llift (fun (p:point)-> p.x)) p

val lallocExample1 : px:int -> py:int -> PureMem int (fun m -> True) (fun m v -> v == px+1)
let lallocExample1 px py =
  pushStackFrame ();
  let sp= lalloc ({x=px ; y=py}) in
  let r = lx sp in
  popStackFrame ();
  (r+1)

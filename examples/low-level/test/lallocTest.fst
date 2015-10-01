(*--build-config
    variables:MATHS=../maths;
    other-files:ext.fst set.fsi set.fst heap.fst st.fst all.fst list.fst stack.fst listset.fst ghost.fst located.fst lref.fst stackAndHeap.fst sst.fst
  --*)

(*perhaps this should be an interface file?*)

module LallocTest
open RST
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
  pushRegion ();
  let sp= lalloc ({x=px ; y=py}) in
  let r = lx sp in
  popRegion ();
  (r+1)

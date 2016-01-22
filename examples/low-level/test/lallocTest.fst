(*--build-config
    variables:MATHS=../maths;
    other-files:FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.List.fst stack.fst listset.fst FStar.Ghost.fst located.fst lref.fst stackAndHeap.fst sst.fst
  --*)

(*perhaps this should be an interface file?*)

module LallocTest
open FStar.Regions.RST
open StackAndHeap
open FStar.Regions.Located
open Heap
open Stack
open Set
open Prims
open List
open FStar.Regions.Heap  open FStar.Regions.Located
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

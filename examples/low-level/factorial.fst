(*--build-config
options: --codegen OCaml-experimental --trace_error --debug yes --prn;
variables:LIB=../../lib;
other-files:$LIB/ext.fst $LIB/set.fsi $LIB/set.fst $LIB/heap.fst $LIB/st.fst $LIB/list.fst stack.fst listset.fst  $LIB/ghost.fst stackAndHeap.fst sst.fst sstCombinators.fst
  --*)
module Factorial
open SSTCombinators
open StackAndHeap
open SST
open Heap
open Stack
open Set
open Prims
open List
open ListSet

val factorial : nat -> Tot nat
let rec factorial n =
match n with
| 0 -> 1
| n -> n * factorial (n - 1)

(* val factorialGuardLC :  n:nat -> li:(ref nat)  -> smem -> type *)
type factorialGuardLC (n:nat) (li : ref nat) (m:smem) =
  (refExistsInMem li m) && (not ((loopkupRef li m) = n))

val factorialGuard :  n:nat -> li:(ref nat)  -> unit
  -> whileGuard (fun m -> b2t (refExistsInMem li m))
                (factorialGuardLC n li)
let factorialGuard n li u = not (memread li = n)
(* the guard of a while loop is not supposed to change the memory*)


type  loopInv (li : ref nat) (res : ref nat) (m:smem) =
  refExistsInMem li m /\ refExistsInMem res m
    /\ (loopkupRef res m = factorial (loopkupRef li m))
    /\ (~ (li = res))

open Ghost
val factorialLoopBody :
  n:nat -> li:(ref nat) -> res:(ref nat)
  -> unit ->
  whileBody (loopInv li res) (factorialGuardLC n li)
    (* (gunion (gonly li) (gonly res)) *)
 (hide (union (singleton (Ref li)) (singleton (Ref res))))
      (*SST unit (fun m -> loopInv li res (mtail m)) (fun m0 _ m1 -> loopInv li res (mtail m1))*)
let factorialLoopBody (n:nat) (li:(ref nat)) (res:(ref nat)) u =
  let liv = memread li in
  let resv = memread res in
  memwrite li (liv + 1);
  memwrite res ((liv+1) * resv)

val factorialLoop : n:nat -> li:(ref nat) -> res:(ref nat)
  -> Mem unit (fun m -> mreads li 0 m /\ mreads res 1 m  /\ ~(li=res))
              (fun m0 _ m1 -> mreads res (factorial n) m1)
              (hide (union (singleton (Ref li)) (singleton (Ref res))))
let factorialLoop (n:nat) (li:(ref nat)) (res:(ref nat)) =
  scopedWhile
    (loopInv li res)
    (factorialGuardLC n li)
    (factorialGuard n li)
    (hide (union (singleton (Ref li)) (singleton (Ref res))))
    (factorialLoopBody n li res)

(*val factorialLoop2 : n:nat -> li:(ref nat) -> res:(ref nat)
  -> Mem unit (fun m -> mreads li 0 m /\ mreads res 1 m  /\ ~(li=res))
              (fun m0 _ m1 -> mreads res (factorial n) m1)
let factorialLoop2 (n:nat) (li:(ref nat)) (res:(ref nat)) =
  scopedWhile1
    li
    (fun liv -> not (liv = 1))
    (loopInv li res)
    (factorialLoopBody n li res)*)


val loopyFactorial : n:nat
  -> WNSC nat (fun m -> True)
              (fun _ rv _ -> (rv == (factorial n)))
              (hide empty)
let loopyFactorial n =
  let li = salloc 0 in
  let res = salloc 1 in
  (factorialLoop n li res);
  let v=memread res in
  v

val loopyFactorial2 : n:nat
  -> Mem nat (fun m -> True)
              (fun _ rv _ -> rv == (factorial n))
              (hide empty)
let loopyFactorial2 n =
  withNewScope
  #nat
  #(fun m -> True) (*same as the comment below. F* should certainly try this precondition*)
  #(fun _ rv _ -> rv == (factorial n)) (*this is the same as that of the conclusion, why cant it be inferred?*)
  #(hide empty)
  (fun u ->
    let li:(ref nat) = salloc 0 in
    let res:(ref nat) = salloc 1 in
    (scopedWhile1
      li
      (fun liv -> not (liv = n))
      (loopInv li res)
      (hide (union (singleton (Ref li)) (singleton (Ref res))))
      (fun u ->
        let liv = memread li in
        let resv = memread res in
        memwrite li (liv + 1);
        memwrite res ((liv+1) * resv)));
    let v=memread res in v)

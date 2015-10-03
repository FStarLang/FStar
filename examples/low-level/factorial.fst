(*--build-config
other-files:ext.fst set.fsi set.fst heap.fst st.fst all.fst list.fst stack.fst listset.fst ghost.fst located.fst lref.fst stackAndHeap.fst sst.fst sstCombinators.fst
  --*)
module Factorial
open RSTCombinators
open StackAndHeap
open RST
open FStar.Heap
open Lref  open Located
open Stack
open FStar.Set
open FStar.List
open ListSet
open FStar.Ghost

val factorial : nat -> Tot nat
let rec factorial n =
match n with
| 0 -> 1
| n -> n * factorial (n - 1)

(* val factorialGuardLC :  n:nat -> li:(lref nat)  -> smem -> type *)
type factorialGuardLC (n:nat) (li : lref nat) (m:smem) =
  (refIsLive li m) && (not ((lookupRef li m) = n))

val factorialGuard :  n:nat -> li:(lref nat)  -> unit
  -> whileGuard (fun m -> b2t (refIsLive li m))
                (factorialGuardLC n li)
let factorialGuard n li u = not (memread li = n)
(* the guard of a while loop is not supposed to change the memory*)


type  loopInv (li : lref nat) (res : lref nat) (m:smem) =
  refIsLive li m /\ refIsLive res m
    /\ (lookupRef res m = factorial (lookupRef li m))
    /\ (~ (li = res))

val factorialLoopBody :
  n:nat -> li:(lref nat) -> res:(lref nat)
  -> unit ->
  whileBody (loopInv li res) (factorialGuardLC n li)
  (hide (union (singleton (Ref li)) (singleton (Ref res))))
      (*RST unit (fun m -> loopInv li res (mtail m)) (fun m0 _ m1 -> loopInv li res (mtail m1))*)
let factorialLoopBody (n:nat) (li:(lref nat)) (res:(lref nat)) u =
  let liv = memread li in
  let resv = memread res in
  memwrite li (liv + 1);
  memwrite res ((liv+1) * resv)
 (*  (eunionUnion li res)*)
val factorialLoop : n:nat -> li:(lref nat) -> res:(lref nat)
  -> Mem unit (fun m -> contains li 0 m /\ contains res 1 m  /\ ~(li=res))
              (fun m0 _ m1 -> contains res (factorial n) m1)
              (hide (union (singleton (Ref li)) (singleton (Ref res))))
let factorialLoop (n:nat) (li:(lref nat)) (res:(lref nat)) =
  scopedWhile
    (loopInv li res)
    (factorialGuardLC n li)
    (factorialGuard n li)
    (hide (union (singleton (Ref li)) (singleton (Ref res))))
    (factorialLoopBody n li res)

(*val factorialLoop2 : n:nat -> li:(lref nat) -> res:(lref nat)
  -> Mem unit (fun m -> contains li 0 m /\ contains res 1 m  /\ ~(li=res))
              (fun m0 _ m1 -> contains res (factorial n) m1)
let factorialLoop2 (n:nat) (li:(lref nat)) (res:(lref nat)) =
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
  let li = ralloc 0 in
  let res = ralloc 1 in
  (factorialLoop n li res);
  let v=memread res in
  v

val loopyFactorial2 : n:nat
  -> Mem nat (fun m -> True)
              (fun _ rv _ -> rv == (factorial n))
              (hide empty)
let loopyFactorial2 n =
  pushRegion ();
    let li:(lref nat) = ralloc 0 in
    let res:(lref nat) = ralloc 1 in
    (scopedWhile1
      li
      (fun liv -> not (liv = n))
      (loopInv li res)
      (eunion (only  li) (only res))
      (fun u ->
        let liv = memread li in
        let resv = memread res in
        memwrite li (liv + 1);
        memwrite res ((liv+1) * resv)));
    let v=memread res in
    popRegion (); v

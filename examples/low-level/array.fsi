(*--build-config
    options:--admit_fsi Set --z3timeout 10;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst  stack.fst listset.fst
    $LIB/ghost.fst stackAndHeap.fst sst.fst sstCombinators.fst $LIB/constr.fst word.fst $LIB/seq.fsi $LIB/seq.fst
  --*)


module Array
open SSTCombinators
open StackAndHeap
open SST
open MachineWord
open Heap
open Set
open Stack
open Seq

(*to make vector opaque, just include vector.fsi*)
(*val testf : vector nat 10 -> nat
let testf v = v 1*)

type array : Type -> Type
open Ghost

(*making it GTot causes a strange error in the postcondition of readIndex *)
val asRef : #a:Type  -> va:(array a) -> Tot (erased (ref (seq a)))


val length: #a:Type -> x:array a -> PureMem nat
  (requires (fun h -> refExistsInMem (reveal (asRef x)) h))
  (ensures  (fun h y _ ->  (refExistsInMem (reveal (asRef x)) h /\ y= ((Seq.length) ((loopkupRef) (reveal (asRef x)) h)))))

(*using the 2 definitions below causes a strange error in readIndex amd updIndex*)
(*val arrayExistsInMem : #a:Type -> (array a) -> smem -> GTot bool
let arrayExistsInMem v sm = refExistsInMem (reveal (asRef v)) sm

val lookup : #a:Type  -> va:(array a) -> m:smem{(arrayExistsInMem va m)} -> GTot ((vector a (length va)))
let lookup 'a va m = (admit ())*)

(*loopkupRef (asRef va) m*)

val readIndex :  #a:Type  -> r:(array a)
  -> index:nat
  -> PureMem a
        (requires (fun m ->  (refExistsInMem (reveal (asRef r)) m) /\ index < Seq.length (loopkupRef (reveal (asRef r)) m) ) )
        (ensures (fun m v _->
          (refExistsInMem (reveal (asRef r)) m) /\ index < Seq.length (loopkupRef (reveal (asRef r)) m) /\ v = Seq.index (loopkupRef (reveal (asRef r)) m) index ))

val writeIndex :  #a:Type -> r:((array a))
  -> index:nat -> newV:a ->
 Mem unit
    (requires (fun m ->  (refExistsInMem (reveal (asRef r)) m) /\ index < Seq.length (loopkupRef (reveal (asRef r)) m) ) )
    (ensures ( fun m0 _ m1 ->
        (refExistsInMem (reveal (asRef r)) m0) /\ index < Seq.length (loopkupRef (reveal (asRef r)) m0) /\
          (m1 = (writeMemAux (reveal (asRef r)) m0 (Seq.upd (loopkupRef (reveal (asRef r)) m0) index newV)))))
      (gonly (reveal (asRef r)))

(*There is no way to read or write a whole vector in non-ghost mode *)
(*create an array on stack*)
val screate :  #a:Type -> init:(seq a)
  -> Mem (array a)
        (requires  (fun m -> (isNonEmpty (st m))))
        (ensures (fun m0 vv m1->
            (isNonEmpty (st m0)) /\ (isNonEmpty (st m1))
            /\ allocateInBlock (reveal (asRef vv)) (topstb m0) (topstb m1) init
            /\ refLoc (reveal (asRef vv)) = InStack (topstid m0) /\ (topstid m0 = topstid m1)
            /\ mtail m0 = mtail m1))
        (hide empty)

(*create an array on the heap*)
val hcreate :  #a:Type -> init:(seq a)
  -> Mem (array a)
        (requires  (fun m -> True))
        (ensures (fun m0 v m1->
            allocateInBlock (reveal (asRef v)) (hp m0) (hp m1) init
            /\ refLoc (reveal (asRef v)) = InHeap /\ (snd m0 = snd m1)))
        (hide empty)

(* This should be removed?*)
val to_seq :  #a:Type  -> r:(array a)
  -> PureMem (seq a)
        (requires (fun m -> b2t (refExistsInMem (reveal (asRef r)) m)))
        (ensures (fun m v _-> (refExistsInMem (reveal (asRef r)) m) /\ v = (loopkupRef (reveal (asRef r)) m)))

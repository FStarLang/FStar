(*--build-config
    options:--admit_fsi FStar.Set --z3timeout 10;
    other-files:ext.fst set.fsi heap.fst st.fst all.fst list.fst  stack.fst listset.fst
    ghost.fst located.fst lref.fst regions.fst rst.fst sstCombinators.fst constr.fst word.fst seq.fsi seq.fst
  --*)


module RSTArray
open SSTCombinators
open RST
open MachineWord
open FStar.Heap
open Lref  open Located
open FStar.Set
open Stack
open Regions
open FStar.Seq

(*to make vector opaque, just include vector.fsi*)
(*val testf : vector nat 10 -> nat
let testf v = v 1*)

type sstarray : Type -> Type
open FStar.Ghost

(*making it GTot causes a strange error in the postcondition of readIndex *)
val asRef : #a:Type  -> va:(sstarray a) -> Tot (erased (lref (seq a)))


val length: #a:Type -> x:sstarray a -> PureMem nat
  (requires (fun h -> refIsLive (reveal (asRef x)) h))
  (ensures  (fun h y ->  (refIsLive (reveal (asRef x)) h /\ y= ((Seq.length) ((lookupRef) (reveal (asRef x)) h)))))

(*using the 2 definitions below causes a strange error in readIndex amd updIndex*)
(*val arrayExistsInMem : #a:Type -> (sstarray a) -> smem -> GTot bool
let arrayExistsInMem v sm = refIsLive (reveal (asRef v)) sm

val lookup : #a:Type  -> va:(sstarray a) -> m:smem{(arrayExistsInMem va m)} -> GTot ((vector a (length va)))
let lookup 'a va m = (admit ())*)

(*lookupRef (asRef va) m*)

val readIndex :  #a:Type  -> r:(sstarray a)
  -> index:nat
  -> PureMem a
        (requires (fun m ->  (refIsLive (reveal (asRef r)) m) /\ index < Seq.length (lookupRef (reveal (asRef r)) m) ) )
        (ensures (fun m v->
          (refIsLive (reveal (asRef r)) m) /\ index < Seq.length (lookupRef (reveal (asRef r)) m)
          /\ v = Seq.index (lookupRef (reveal (asRef r)) m) index ))

val writeIndex :  #a:Type -> r:((sstarray a))
  -> index:nat -> newV:a ->
 Mem unit
    (requires (fun m ->  (refIsLive (reveal (asRef r)) m) /\ index < Seq.length (lookupRef (reveal (asRef r)) m) ) )
    (ensures ( fun m0 _ m1 ->
        (refIsLive (reveal (asRef r)) m0) /\ index < Seq.length (lookupRef (reveal (asRef r)) m0) /\
          (m1 = (writeMemAux (reveal (asRef r)) m0 (Seq.upd (lookupRef (reveal (asRef r)) m0) index newV)))))
      (only (reveal (asRef r)))

(*create an sstarray on stack*)
val screateSeq :  #a:Type -> init:(seq a)
  -> Mem (sstarray a)
        (requires  (fun m -> (isNonEmpty (st m))))
        (ensures (fun m0 vv m1->
            (isNonEmpty (st m0)) /\ (isNonEmpty (st m1))
            /\ allocatedInRegion (reveal (asRef vv)) (topRegion m0) (topRegion m1) init
            /\ regionOf (reveal (asRef vv)) = InStack (topRegionId m0) /\ (topRegionId m0 = topRegionId m1)
            /\ tail m0 = tail m1))
        (hide empty)

(*create an sstarray on the heap*)
//TODO: we should remove this one; currently used only in MD5 for some experiments
val hcreateSeq :  #a:Type -> init:(seq a)
  -> Mem (sstarray a)
        (requires  (fun m -> True))
        (ensures (fun m0 v m1->
            allocatedInRegion (reveal (asRef v)) (hp m0) (hp m1) init
            /\ regionOf (reveal (asRef v)) = InHeap /\ (snd m0 = snd m1)))
        (hide empty)

val screate :  #a:Type -> len:nat -> init:a
  -> Mem (sstarray a)
        (requires  (fun m -> (isNonEmpty (st m))))
        (ensures (fun m0 vv m1->
            (isNonEmpty (st m0)) /\ (isNonEmpty (st m1))
            /\ allocatedInRegion (reveal (asRef vv)) (topRegion m0) (topRegion m1) (Seq.create len init)
            /\ regionOf (reveal (asRef vv)) = InStack (topRegionId m0) /\ (topRegionId m0 = topRegionId m1)
            /\ tail m0 = tail m1))
        (hide empty)

val hcreate :  #a:Type -> len:nat -> init:a
  -> Mem (sstarray a)
        (requires  (fun m -> True))
        (ensures (fun m0 v m1->
            allocatedInRegion (reveal (asRef v)) (hp m0) (hp m1) (Seq.create len init)
            /\ regionOf (reveal (asRef v)) = InHeap /\ (snd m0 = snd m1)))
        (hide empty)


(* This is convenient. It need not be a Primitive, but can be implemented.
   For short arrays, such as the MD5 checksum (4 words), it might not be too inefficient*)
val to_seq :  #a:Type  -> r:(sstarray a)
  -> PureMem (seq a)
        (requires (fun m -> b2t (refIsLive (reveal (asRef r)) m)))
        (ensures (fun m v-> (refIsLive (reveal (asRef r)) m) /\ v = (lookupRef (reveal (asRef r)) m)))

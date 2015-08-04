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

(*making it GTot causes a strange error in the postcondition of readIndex *)
val asRef : #a:Type  -> va:(array a) -> Tot (ref (seq a))


val length: #a:Type -> x:array a -> PureMem nat
  (requires (fun h -> refExistsInMem (asRef x) h))
  (ensures  (fun h y _ ->  (refExistsInMem (asRef x) h /\ y=Seq.length (loopkupRef (asRef x) h))))

(*using the 2 definitions below causes a strange error in readIndex amd updIndex*)
(*val arrayExistsInMem : #a:Type -> (array a) -> smem -> GTot bool
let arrayExistsInMem v sm = refExistsInMem (asRef v) sm

val lookup : #a:Type  -> va:(array a) -> m:smem{(arrayExistsInMem va m)} -> GTot ((vector a (length va)))
let lookup 'a va m = (admit ())*)

(*loopkupRef (asRef va) m*)

val readIndex :  #a:Type  -> r:(array a)
  -> index:nat
  -> PureMem a
        (requires (fun m ->  (refExistsInMem (asRef r) m) /\ index < Seq.length (loopkupRef (asRef r) m) ) )
        (ensures (fun m v _->
          (refExistsInMem (asRef r) m) /\ index < Seq.length (loopkupRef (asRef r) m) /\ v = Seq.index (loopkupRef (asRef r) m) index ))

val writeIndex :  #a:Type -> r:((array a))
  -> index:nat -> newV:a ->
 Mem unit
    (requires (fun m ->  (refExistsInMem (asRef r) m) /\ index < Seq.length (loopkupRef (asRef r) m) ) )
    (ensures ( fun m0 _ m1 ->
        (refExistsInMem (asRef r) m0) /\ index < Seq.length (loopkupRef (asRef r) m0) /\
          (m1 = (writeMemAux (asRef r) m0 (Seq.upd (loopkupRef (asRef r) m0) index newV)))))
      (singleton (Ref (asRef r)))

(*There is no way to read or write a whole vector in non-ghost mode *)

(*create an array on stack*)
val screate :  #a:Type -> init:(seq a)
  -> Mem (array a)
        (requires  (fun m -> (isNonEmpty (st m))))
        (ensures (fun m0 vv m1->
            (isNonEmpty (st m0)) /\ (isNonEmpty (st m1))
            /\ allocateInBlock (asRef vv) (topstb m0) (topstb m1) init
            /\ refLoc (asRef vv) = InStack (topstid m0) /\ (topstid m0 = topstid m1)
            /\ mtail m0 = mtail m1))
        (empty)

(*create an array on the heap*)
val hcreate :  #a:Type -> init:(seq a)
  -> Mem (array a)
        (requires  (fun m -> True))
        (ensures (fun m0 v m1->
            allocateInBlock (asRef v) (hp m0) (hp m1) init
            /\ refLoc (asRef v) = InHeap /\ (snd m0 = snd m1)))
        (empty)

val to_seq :  #a:Type  -> r:(array a)
  -> PureMem (seq a)
        (requires (fun m -> b2t (refExistsInMem (asRef r) m)))
        (ensures (fun m v _-> (refExistsInMem (asRef r) m) /\ v = (loopkupRef (asRef r) m)))

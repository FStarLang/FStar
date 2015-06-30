(*--build-config
    options:--admit_fsi Set --z3timeout 10;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst  stack.fst listset.fst st3.fst $LIB/constr.fst word.fst mvector.fsi mvector.fst
  --*)

module Array
open StructuredMem
open MachineWord
open Heap
open Set
open Stack
open MVector

type array : Type -> Type

val length : #a:Type -> (array a) -> Tot nat

(*making it GTot causes a strange error in the postcondition of readIndex *)
val asRef : #a:Type  -> va:(array a) -> Tot (ref (vector a (length va)))

(*using the 2 definitions below causes a strange error in readIndex amd updIndex*)
(*val arrayExistsInMem : #a:Type -> (array a) -> smem -> GTot bool
let arrayExistsInMem v sm = refExistsInMem (asRef v) sm

val lookup : #a:Type  -> va:(array a) -> m:smem{(arrayExistsInMem va m)} -> GTot ((vector a (length va)))
let lookup 'a va m = (admit ())*)

(*loopkupRef (asRef va) m*)

val readIndex :  #a:Type  -> r:(array a)
  -> index:nat{index < length r}
  -> PureMem a
        (requires (fun m -> b2t (refExistsInMem (asRef r) m)))
        (ensures (fun m v _-> (refExistsInMem (asRef r) m) /\ v = atIndex (loopkupRef (asRef r) m) index))

val writeIndex :  #a:Type -> r:((array a))
  -> index:nat{index<length r} -> newV:a ->
 Mem unit
    (requires (fun m -> b2t (refExistsInMem (asRef r) m)))
    (ensures (fun m0 _ m1-> (refExistsInMem (asRef r) m0) /\ m1 = (writeMemAux (asRef r)  m0 (updateIndex (loopkupRef (asRef r) m0) index newV))))
      (singleton (Ref (asRef r)))

(*There is no way to read or write a whole vector in non-ghost mode *)

(*create an array on stack*)
val screateArray :  #a:Type  -> #n:nat -> init:(vector a n)
  -> Mem (array a)
        (requires  (fun m -> (isNonEmpty (st m))))
        (ensures (fun m0 v m1->
            (isNonEmpty (st m0)) /\ (isNonEmpty (st m1)) /\ length v = n
            /\ allocateInBlock (asRef v) (topstb m0) (topstb m1) init
            /\ refLoc (asRef v) = InStack (topstid m0) /\ (topstid m0 = topstid m1)
            /\ mtail m0 = mtail m1))
        (empty)

(*create an array on the heap*)
val hcreateArray :  #a:Type  -> #n:nat -> init:(vector a n)
  -> Mem (array a)
        (requires  (fun m -> True))
        (ensures (fun m0 v m1->
            length v = n
            /\ allocateInBlock (asRef v) (hp m0) (hp m1) init
            /\ refLoc (asRef v) = InHeap /\ (snd m0 = snd m1)))
        (empty)

val readArray :  #a:Type  -> r:(array a)
  -> PureMem (vector a (length r))
        (requires (fun m -> b2t (refExistsInMem (asRef r) m)))
        (ensures (fun m v _-> (refExistsInMem (asRef r) m) /\ v = (loopkupRef (asRef r) m)))

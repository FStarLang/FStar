(*--build-config
    options:--admit_fsi Set --z3timeout 100;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/list.fst  stack.fst listset.fst
    $LIB/ghost.fst stackAndHeap.fst sst.fst sstCombinators.fst $LIB/constr.fst word.fst $LIB/seq.fsi $LIB/seq.fst array.fsi array.fst
  --*)

module ArrayAlgos
open SSTCombinators
open StackAndHeap
open SST
open MVector
open Heap
open Set
open MachineWord
open SSTArray
open MD5Common
open Seq
open Ghost

val contains : #a:Type -> smem -> sstarray a -> GTot bool
let contains m v =
refExistsInMem (reveal (asRef v)) m

val eonly :  #a:Type -> sstarray a -> Tot modset
let eonly s = (eonly (asRef s))


val sel : #a:Type -> m:smem -> v:(sstarray a){contains m v} -> GTot (seq a)
let sel m v = loopkupRef (reveal (asRef v)) m

val loopkupRefR : a:Type -> m:smem -> r:(ref a) ->
  Pure a (requires (refExistsInMem r m)) (ensures (fun _ -> True))
let loopkupRefR (a:Type) m r = loopkupRef r m

val loopkupRefR2 : a:Type -> m:smem -> r:(ref a){(refExistsInMem r m)} ->Tot a
let loopkupRefR2 (a:Type) m r = loopkupRef r m


val eloopkupRef : #a:Type -> m:smem -> r:(erased (ref a)){(refExistsInMem (reveal r) m)} ->
  Tot (erased a)
let eloopkupRef  (#a:Type) m v = (elift1_p #(ref a) #a #(fun r -> b2t (refExistsInMem r m)) (loopkupRefR2 a m)) v


val esel : #a:Type -> m:smem -> v:(sstarray a){refExistsInMem (reveal (asRef v)) m} -> Tot (erased (seq a))
let esel (#a:Type) m v = eloopkupRef m (asRef v)

val eeloopkupRef : #a:Type -> m:(erased smem) -> r:(erased (ref a)){(refExistsInMem (reveal r) (reveal m))} ->
  Tot (erased a)
let eeloopkupRef  (#a:Type) m v = (elift2_p #smem #(ref a) #(fun m r -> b2t (refExistsInMem r m)) #a (loopkupRefR2)) m v

val eesel : #a:Type -> m:(erased smem) -> v:(sstarray a){refExistsInMem (reveal (asRef v)) (reveal m)} -> Tot (erased (seq a))
let eesel (#a:Type) m v = eeloopkupRef m (asRef v)


val glength : #a:Type -> v:(sstarray a) -> m:smem{contains m v} -> GTot nat
let glength v m = Seq.length (sel m v)

val haslength : #a:Type -> smem -> sstarray a -> n:nat -> GTot bool
let haslength m v n = contains m v && glength v m = n

type lseq (a:Type) (n:nat) = x:(seq a){Seq.length x =n}

val eeseln : #a:Type -> n:nat -> m:(erased smem) -> v:(sstarray a){haslength (reveal m) v n} -> Tot (erased (lseq a n))
let eeseln (#a:Type) n m v = (elift2_p #smem #(ref a) #(fun m r -> refExistsInMem r m /\ Seq.length (loopkupRef r m) = n)
  #(lseq a n) (loopkupRefR2)) m (asRef v)

val seqAsFun : #a:Type -> n:nat -> s:(seq a){Seq.length s= n}
  -> Tot ((k:nat{k<n}) -> Tot a)
let seqAsFun n s = (fun k -> index s k)

val arrayAsFun : #a:Type -> n:nat -> m:smem -> v:(sstarray a){haslength m v n}
  -> Tot (erased ((k:nat{k<n}) -> Tot a))
let arrayAsFun (#a:Type) n m v = (elift1_p #_ #_ #(fun sq -> Seq.length sq ==n) (seqAsFun #a n)) (esel m v)

type prefixEqual  (#a:Type)
  (v1: seq a) (v2: seq a) (p:nat{p <= length v1 /\ p<= length v2})
  = forall (n:nat{n<p}). index v1 n = index v2 n

(*val prefixInc: a#Type -> n:nat->
  (m1 = (writeMemAux (asRef r) m0 (Seq.upd (loopkupRef (asRef r) m0) index newV)))*)

type prefixEqualL  (#a:Type)
  (v1: seq a) (v2:(seq a))
  = length v1 <= length v2 /\ (forall (n:nat{n<length v1}). index v1 n = index v2 n)

(* Helper functions for stateful sstarray manipulation *)
val copy:
  #a:Type -> s:sstarray a -> scp :sstarray a
  -> WNSC unit
     (requires (fun h -> contains h s /\ contains h scp /\ glength s h <= glength scp h))
     (ensures (fun h0 _ h1 -> (contains h1 s) /\  (contains h1 scp)
                /\ (glength  s h1  <= glength  scp h1)
                /\ prefixEqualL (sel h1 s) (sel h1 scp)
                /\ (contains h0 scp) /\ glength scp h0 = glength scp h1
              ))
     ((elift1 only) (asRef scp))

let copy s scp =
  let ctr = salloc #nat 0 in
  let len = SSTArray.length s in
  let lenscp = SSTArray.length scp in
  scopedWhile1
    ctr
    (fun ctrv -> ctrv < len)
    (fun m -> contains m s /\ contains m scp
        /\ len = glength s m /\ lenscp = glength scp m
          /\ refExistsInMem ctr m
          /\ (loopkupRef ctr m) <=len
          /\ prefixEqual (sel m s) (sel m scp) (loopkupRef ctr m)
          )
    (gunion ((elift1 only) (asRef scp)) (gonly ctr))
    (fun u -> let ctrv = memread ctr in
              writeIndex scp ctrv (readIndex s ctrv);
              memwrite ctr (ctrv +1 ))

(* sclone does not make sense*)
val hcloneAux:
  #a:Type -> s:sstarray a
  -> Mem (sstarray a)
     (requires (fun h -> contains h s /\ 0 < glength s h ))
     (ensures (fun h0 scp h1 -> (contains h1 s) /\  (contains h1 scp)
                /\ (glength s h1) = (glength scp h1)
                /\ Seq.Eq (sel h1 s) (sel h1 scp)
              ))
     (hide empty)

let hcloneAux s =
  let scp = hcreate  (SSTArray.length s) (readIndex s 0) in
    pushStackFrame ();
      copy s scp;
    popStackFrame ();
    scp

(*Since we always use the Mem abbreviation and never SST directly,
  withNewScope does not have any advantage over pushStackFrame/popStackFrame.
  The definition of Mem prevents one from improperly pushing/popping
    of stack frames; i.e. any computation of type Mem ....
    must pop exactly all the stack frames it pushed
  *)

    (*let hcloneAux s =
      let scp = hcreate (Seq.create (SSTArray.length s) (readIndex s 0)) in
        withNewScope
          #_ (*the pre/post conditions below just come from the definition of copy. It is annoying that they cannot be inferred*)
          #((fun h -> contains h s /\ contains h scp /\ glength s h <= glength scp h))
          #((fun h0 _ h1 -> (contains h1 s) /\  (contains h1 scp)
                   /\ (glength  s h1  <= glength  scp h1)
                   /\ prefixEqualL (sel h1 s) (sel h1 scp)
                   /\ (contains h0 scp) /\ glength scp h0 = glength scp h1
                 ))
          #(only (asRef scp))
          (fun u -> copy s scp);
        scp*)



(*allow creation of uninitialized arrays? ,
  but use the type system to prevent reading of uninitialized indices?

  Currently, there might be some wasted computation in initializing an array
  that will immediately be written into.
*)


val hclone:
  #a:Type -> s:sstarray a
  -> Mem (sstarray a)
     (requires (fun h -> contains h s))
     (ensures (fun h0 scp h1 -> (contains h1 s) /\  (contains h1 scp)
                /\ (glength s h1) = (glength scp h1)
                /\ Seq.Eq (sel h1 s) (sel h1 scp)
              ))
     (hide empty)

let hclone 'a s =
  if (SSTArray.length s = 0)
  then  s
  else hcloneAux s

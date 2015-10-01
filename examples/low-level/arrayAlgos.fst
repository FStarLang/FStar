(*--build-config
    options:--admit_fsi Set --z3timeout 100;
    other-files:ext.fst set.fsi heap.fst st.fst all.fst list.fst  stack.fst listset.fst
    ghost.fst located.fst lref.fst stackAndHeap.fst sst.fst sstCombinators.fst constr.fst word.fst seq.fsi seq.fst array.fsi array.fst
  --*)

module ArrayAlgos
open RSTCombinators
open StackAndHeap
open RST
open MVector
open Heap
open Lref  open Located
open FStar.Set
open MachineWord
open RSTArray
open MD5Common
open FStar.Seq
open FStar.Ghost

val liveArr : #a:Type -> smem -> sstarray a -> GTot bool
let liveArr m v =
liveRef (reveal (asRef v)) m

val eonly :  #a:Type -> sstarray a -> Tot modset
let eonly s = (eonly (asRef s))


val sel : #a:Type -> m:smem -> v:(sstarray a){liveArr m v} -> GTot (seq a)
let sel m v = lookupRef (reveal (asRef v)) m

val lookupRefR : #a:Type -> #post:(a->Type) -> m:smem -> r:(lref a) ->

  Pure a (requires (liveRef r m /\ post (lookupRef r m)))
    (ensures (fun ret -> post ret))
let lookupRefR m r = lookupRef r m

val lookupRefR2 : a:Type -> m:smem -> r:(lref a){(liveRef r m)} ->Tot a
let lookupRefR2 (a:Type) m r = lookupRef r m


val elookupRef : #a:Type -> m:smem -> r:(erased (lref a)){(liveRef (reveal r) m)} ->
  Tot (erased a)
let elookupRef  (#a:Type) m v = (elift1_p #(lref a) #a #(fun r -> b2t (liveRef r m)) (lookupRefR2 a m)) v


val esel : #a:Type -> m:smem -> v:(sstarray a){liveRef (reveal (asRef v)) m} -> Tot (erased (seq a))
let esel (#a:Type) m v = elookupRef m (asRef v)

val eelookupRef : #a:Type -> m:(erased smem) -> r:(erased (lref a)){(liveRef (reveal r) (reveal m))} ->
  Tot (erased a)
let eelookupRef  (#a:Type) m v =
  (elift2_p #smem #(lref a) #(fun m r -> b2t (liveRef r m)) #a (lookupRefR2)) m v

val eesel : #a:Type -> m:(erased smem)
-> v:(sstarray a){liveRef (reveal (asRef v)) (reveal m)} -> Tot (erased (seq a))
let eesel (#a:Type) m v = eelookupRef m (asRef v)


val glength : #a:Type -> v:(sstarray a) -> m:smem{liveArr m v} -> GTot nat
let glength v m = Seq.length (sel m v)

val gindex: #a:Type -> v:(sstarray a) -> m:smem {liveArr m v} -> i:nat{i < glength v m} -> GTot a
let gindex v m i = Seq.index (sel m v) i

val haslength : #a:Type -> smem -> sstarray a -> n:nat -> GTot bool
let haslength m v n = liveArr m v && glength v m = n

type lseq (a:Type) (n:nat) = x:(seq a){Seq.length x =n}

val seqAsFun : #a:Type -> n:nat -> s:(seq a){Seq.length s= n}
  -> Tot ((k:nat{k<n}) -> Tot a)
let seqAsFun n s = (fun k -> index s k)

val arrayAsFun : #a:Type -> n:nat -> m:smem -> v:(sstarray a){haslength m v n}
  -> Tot (erased ((k:nat{k<n}) -> Tot a))
let arrayAsFun (#a:Type) n m v = (elift1_p #_ #_ #(fun sq -> Seq.length sq ==n) (seqAsFun #a n)) (esel m v)

val eeseln : #a:Type -> n:nat -> m:(erased smem) -> v:(sstarray a){haslength (reveal m) v n}
  -> Tot (erased (lseq a n))
let eeseln (#a:Type) n m v = (elift1_p #_ #_ #(fun sq -> Seq.length sq ==n) (fun x -> x)) (eesel m v)

(*
some failed attempts below. It is surprising how the above works, but not the ones below

val eeseln : #a:Type -> n:nat -> m:(erased smem)
  -> v:(sstarray a) ->
    Pure (erased (seq a)) (requires ( liveRef (reveal (asRef v)) (reveal m)
          /\  Seq.length (lookupRef (reveal (asRef v)) (reveal m)) = n))
                          (ensures (fun rs -> Seq.length (reveal rs) = n))
let eeseln (#a:Type) n m v =
  let s = eesel m v in
  admitP (b2t (Seq.length (reveal s)=n)); s

(elift2_wp #smem #(lref (seq a)) #(seq a)
  #(fun m r -> liveRef r m
        /\  Seq.length (lookupRef r m) = n
          )
  #(fun m r rs ->
        b2t (Seq.length rs = n)
          )
  (lookupRefR #(seq a) #(fun (s:seq a) -> b2t (Seq.length s = n))) ) m (asRef v)

*)

type prefixEqual  (#a:Type)
  (v1: seq a) (v2: seq a) (p:nat{p <= length v1 /\ p<= length v2})
  = forall (n:nat{n<p}). index v1 n = index v2 n

(*val prefixInc: a#Type -> n:nat->
  (m1 = (writeMemAux (asRef r) m0 (Seq.upd (lookupRef (asRef r) m0) index newV)))*)

type prefixEqualL  (#a:Type)
  (v1: seq a) (v2:(seq a))
  = length v1 <= length v2 /\ (forall (n:nat{n<length v1}). index v1 n = index v2 n)

(* Helper functions for stateful sstarray manipulation *)
val copy:
  #a:Type -> s:sstarray a -> scp :sstarray a
  -> WNSC unit
     (requires (fun h -> liveArr h s /\ liveArr h scp /\ glength s h <= glength scp h))
     (ensures (fun h0 _ h1 -> (liveArr h1 s) /\  (liveArr h1 scp)
                /\ (glength  s h1  <= glength  scp h1)
                /\ prefixEqualL (sel h1 s) (sel h1 scp)
                /\ (liveArr h0 scp) /\ glength scp h0 = glength scp h1
              ))
     (eonly scp)

let copy s scp =
  let ctr = ralloc #nat 0 in
  let len = RSTArray.length s in
  let lenscp = RSTArray.length scp in
  scopedWhile1
    ctr
    (fun ctrv -> ctrv < len)
    (fun m -> liveArr m s /\ liveArr m scp
        /\ len = glength s m /\ lenscp = glength scp m
          /\ liveRef ctr m
          /\ (lookupRef ctr m) <=len
          /\ prefixEqual (sel m s) (sel m scp) (lookupRef ctr m)
          )
    (eunion (eonly scp) (only ctr))
    (fun u -> let ctrv = memread ctr in
              writeIndex scp ctrv (readIndex s ctrv);
              memwrite ctr (ctrv +1 ))

(* sclone does not make sense*)
val hcloneAux:
  #a:Type -> s:sstarray a
  -> Mem (sstarray a)
     (requires (fun h -> liveArr h s /\ 0 < glength s h ))
     (ensures (fun h0 scp h1 -> (liveArr h1 s) /\  (liveArr h1 scp)
                /\ (glength s h1) = (glength scp h1)
                /\ Seq.Eq (sel h1 s) (sel h1 scp)
              ))
     (hide empty)

let hcloneAux s =
  let scp = hcreate  (RSTArray.length s) (readIndex s 0) in
    pushRegion ();
      copy s scp;
    popRegion ();
    scp

(*Since we always use the Mem abbreviation and never RST directly,
  withNewScope does not have any advantage over pushRegion/popRegion.
  The definition of Mem prevents one from improperly pushing/popping
    of stack frames; i.e. any computation of type Mem ....
    must pop exactly all the stack frames it pushed
  *)

    (*let hcloneAux s =
      let scp = hcreate (Seq.create (RSTArray.length s) (readIndex s 0)) in
        withNewScope
          #_ (*the pre/post conditions below just come from the definition of copy. It is annoying that they cannot be inferred*)
          #((fun h -> liveArr h s /\ liveArr h scp /\ glength s h <= glength scp h))
          #((fun h0 _ h1 -> (liveArr h1 s) /\  (liveArr h1 scp)
                   /\ (glength  s h1  <= glength  scp h1)
                   /\ prefixEqualL (sel h1 s) (sel h1 scp)
                   /\ (liveArr h0 scp) /\ glength scp h0 = glength scp h1
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
     (requires (fun h -> liveArr h s))
     (ensures (fun h0 scp h1 -> (liveArr h1 s) /\  (liveArr h1 scp)
                /\ (glength s h1) = (glength scp h1)
                /\ Seq.Eq (sel h1 s) (sel h1 scp)
              ))
     (hide empty)

let hclone 'a s =
  if (RSTArray.length s = 0)
  then  s
  else hcloneAux s

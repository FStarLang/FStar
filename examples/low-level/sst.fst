(*--build-config
    variables:LIB=../../lib;
    variables:MATHS=../maths;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/set.fst $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/list.fst stack.fst listset.fst $LIB/ghost.fst located.fst lref.fst stackAndHeap.fst
  --*)

(*perhaps this should be an interface file?*)

module SST
open StackAndHeap
open Located
open Heap
open Stack
open Set
open Prims
open List
open Lref  open Located
open ListSet

kind Pre  = smem -> Type
kind Post (a:Type) = a -> smem -> Type

effect SST (a:Type) (pre:Pre) (post: (smem -> Post a)) =
        StSTATE a
              (fun (p:Post a) (h:smem) -> pre h /\ (forall a h1. (pre h  /\ post h a h1) ==> p a h1)) (* WP *)
              (fun (p:Post a) (h:smem) -> (forall a h1. (pre h  /\ post h a h1) ==> p a h1))          (* WLP *)

assume val halloc:  #a:Type -> init:a -> SST (lref a)
                                         (fun m -> True)
                                         (fun m0 r m1 -> allocateInBlock r (hp m0)  (hp m1) init /\ (snd m0 = snd m1) /\ refLoc r == InHeap)

assume val salloc:  #a:Type -> init:a -> SST (lref a)
     (fun m -> b2t (isNonEmpty (st m))) (*why is "== true" required here, but not at other places? : *)
     (*Does F* have (user defined?) implicit coercions? : Not yet *)
     (fun m0 r m1 ->
          (isNonEmpty (st m0)) /\ (isNonEmpty (st m1))
          /\ allocateInBlock r (topstb m0) (topstb m1) init
          /\ refLoc r = InStack (topstid m0) /\ (topstid m0 = topstid m1)
          /\ mtail m0 = mtail m1)

assume val memread:  #a:Type -> r:(lref a) -> SST a
	  (fun m -> b2t (liveRef r m))
    (fun m0 a m1 -> m0=m1 /\ (liveRef r m0) /\ loopkupRef r m0 = a)

assume val memwrite:  #a:Type -> r:(lref a) -> v:a ->
  SST unit
	    (fun m -> b2t (liveRef r m))
      (fun m0 _ m1 -> (liveRef r m1)
        /\ (writeMemAux r m0 v) =  m1)

(*
Free can only deallocate a heap-allocated lref. The implementation
below doesn't make sense becasue it allows even deallocation of stack
references

assume val freeRef:  #a:Type -> r:(lref a)  ->
  SST unit
	    (fun m -> b2t (liveRef r m))
      (fun m0 _ m1 -> (freeMemAux r m0) ==  m1)
*)

(*make sure that the ids are monotone *)
assume val pushStackFrame:  unit -> SST unit
    (fun m -> True)
    (fun m0 _ m1 ->
             (mtail m1 = m0)
          /\ (isNonEmpty (st m1))
          /\ topstb m1 = emp)

assume val popStackFrame:  unit -> SST unit
    (fun m -> b2t (isNonEmpty (st m)))
    (fun m0 _ m1 -> mtail m0 ==  m1)


(** Injection of DIV effect into the new effect, mostly copied from prims.fst*)
kind SSTPost (a:Type) = STPost_h smem a


sub_effect
  DIV  ~> StSTATE = fun (a:Type) (wp:PureWP a) (p : SSTPost a) (h:smem)
                -> wp (fun a -> p a h)


effect Mem (a:Type) (pre: smem -> Type) (post: (smem -> SSTPost a)) (mod: modset) =
        SST a pre (fun m0 a m1 -> post m0 a m1 /\ sids m0 = sids m1 /\ canModify m0 m1 mod)

effect PureMem (a:Type) (pre:smem -> Type) (post: ( smem -> a -> Type)) =
        SST a pre (fun m0 a m1 -> post m1 a /\ m0=m1)

open Ghost
assume val get : unit -> PureMem (erased smem)
      (requires (fun m -> true))
      (ensures (fun m v -> reveal v = m))

(*PureMem might seem strange. We need it because lalloc does not
change the map from references to their values.
*)
assume val lalloc: #a:Type -> v:a -> PureMem
  (located a)
  (requires (fun m ->isNonEmpty (st m)))
  (ensures (fun m1 l -> greveal l = v /\ isNonEmpty (st m1) /\ regionOf l = InStack (topstid m1)))


assume val llift : f:('a -> Tot 'b) -> l:located 'a
-> PureMem 'b (requires (fun m-> liveLoc l m))
              (ensures (fun v m1 -> v == f (greveal l) ))

(*--build-config
    options:--admit_fsi Set;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst stack.fst listset.fst
  --*)

module StructuredMem
open Heap
open Stack
open Set
open Prims
open List
open ListSet
type sidt = nat

(*How does List.memT work? is equality always decidable?*)

(* should we way that the stack ids are unique and contained in the list of sidts : {contains (map snd (fst p)) (snd p)}*)
type memStack = x:((Stack (sidt * heap)) * (list sidt))
  {let stids = (mapT fst (fst x)) in
    let idhistory = (snd x) in
    (lsubset stids idhistory) && (noRepeats stids)}

(* should we also include sizes of refs in order to enable reasoninag about memory usage of programs?*)
(* what is the size of programs ?*)
type smem = heap * memStack

(*rename heap to memblock, and then hp to heap*)
let hp (s : smem) = fst s

val st : smem -> Tot (Stack (sidt * heap))
let st (s : smem) = fst (snd s)

let sid (s : (sidt * heap)) = fst s

val topst : (s:smem{isNonEmpty (st s)}) -> Tot  (sidt * heap)
let topst ss = (top (st ss))

val topstb : (s:smem{isNonEmpty (st s)}) ->  Tot heap
let topstb ss = snd (topst ss)

val topstid : (s:smem{isNonEmpty (st s)}) ->  Tot sidt
let topstid ss = fst (topst ss)


new_effect StSTATE = STATE_h smem


kind Pre  = smem -> Type
kind Post (a:Type) = a -> smem -> Type

effect ST (a:Type) (pre:Pre) (post: (smem -> Post a)) =
        StSTATE a
              (fun (p:Post a) (h:smem) -> pre h /\ (forall a h1. (pre h  /\ post h a h1) ==> p a h1)) (* WP *)
              (fun (p:Post a) (h:smem) -> (forall a h1. (pre h  /\ post h a h1) ==> p a h1))          (* WLP *)


type refLocType =
  | InHeap : refLocType
  | InStack : id:sidt -> refLocType

assume val refLoc : #a:Type -> ref a -> Tot refLocType

(*it shpuld be possible to define this*)
assume val blockAtLoc : smem -> refLocType  -> Tot (option heap)


type allocateInBlock (#a:Type) (r: ref a) (h0 : heap) (h1 : heap) (init : a)   = not(Heap.contains h0 r) /\ Heap.contains h1 r /\  h1 == upd h0 r init



assume val halloc:  #a:Type -> init:a -> ST (ref a)
                                         (fun m -> True)
                                         (fun m0 r m1 -> allocateInBlock r (hp m0)  (hp m1) init /\ (st m0 == st m1) /\ refLoc r == InHeap)

assume val salloc:  #a:Type -> init:a -> ST (ref a)
     (fun m -> isNonEmpty (st m) == true) (*why is "== true" required here, but not at other places?*)
     (*Does F* have (user defined?) implicit coercions?*)
     (fun m0 r m1 ->
          (isNonEmpty (st m0)) /\ (isNonEmpty (st m1))
          /\ allocateInBlock r (topstb m0) (topstb m0) init
          /\ refLoc r == InStack (topstid m0) /\ (topstid m0 = topstid m1)
          /\ stail (st m0) == stail (st m1) /\ (hp m0) == hp m1)



val refExistsInMem : #a:Type -> (ref a) -> smem ->  Tot bool
let refExistsInMem (#a:Type) (r:ref a) (m:smem) =
match (blockAtLoc m (refLoc r)) with
          | Some b -> Heap.contains b r
          | None -> false

(* it is surprising that sel always returns something; It might be tricky to implement it.
   What prevents me from creating a ref of an empty type? Perhaps it is impossible to create a member
   of the type (ref False) . For example, the memory allocation operator, which creates a new (ref 'a)
   requires an initial value of type 'a
*)
val loopkupRef : #a:Type -> (ref a) -> smem ->  Tot (option a)
let loopkupRef (#a:Type) (r:ref a) (m:smem) =
match (blockAtLoc m (refLoc r)) with
          | Some b -> Some (sel b r)
          | None -> None

assume val read:  #a:Type -> r:(ref a) -> ST a
	  (fun m -> (refExistsInMem r m) == true)
    (fun m0 a m1 -> m0=m1 /\ loopkupRef r m0 = Some a)



val sids : smem -> Tot (list sidt)
let sids (m : smem) = mapT fst (st m)

assume val newStackFrame:  unit -> ST unit
    (fun m -> True)
    (fun m0 a m1 -> stail (st m1) = (st m0) /\ (isNonEmpty (st m1)) /\ (notIn (topstid m1) (sids m0)) /\ (topstb m1) = emp)


(*
assume val write:  #a:Type -> r:(ref a) -> ST unit
	    (fun m -> (refExistsInMem r m) == true)
      (fun m0 a m1 -> m0=m1 /\ loopkupRef r m0 = Some a)
*)

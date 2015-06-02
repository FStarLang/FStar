(*--build-config
    options:--admit_fsi Set;
    variables:LIB=..;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst stack.fst $LIB/list.fst
  --*)

module StructuredMem
open Heap
open Stack
open Set

type sidt = nat


(* should we way that the stack ids are unique and contained in the list of sidts : {contains (map snd (fst p)) (snd p)}*)
type memStack = ((Stack (sidt * heap)) * (list sidt))
(* should we also include sizes of refs in order to enable reasoninag about memory usage of programs?*)
(* what is the size of programs ?*)
type smem = heap * memStack

(*rename heap to memblock, and then hp to heap*)
let hp (s : smem) = fst s
let st (s : smem) = fst (snd s)
let sid (s : (sidt * heap)) = fst s

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


type allocateInBlock (#a:Type) (r: ref a) (h0 : heap) (h1 : heap) (init : a)   = not(contains h0 r) /\ contains h1 r /\  h1 == upd h1 r init



assume val alloc:  #a:Type -> init:a -> ST (ref a)
                                         (fun m -> True)
                                         (fun m0 r m1 -> allocateInBlock r (hp m0)  (hp m1) init /\ (st m0 == st m1) /\ refLoc r == InHeap)


assume val salloc:  #a:Type -> init:a -> ST (ref a)
                                         (fun m -> True)
                                         (fun m0 r m1 -> exists s0. exists s1. (isTop s0 (st m0)) /\ (isTop s1 (st m1)) /\ allocateInBlock r (snd s0)  (snd s1) init
                                         		/\ refLoc r == InStack (sid s0) /\ sid s0 = sid s1 /\ btail (st m0) == btail (st m1) /\ (hp m0) == hp m1)

assume val read:  #a:Type -> r:(ref a) -> ST a
                                      	    (fun m -> exists b. blockAtLoc m (refLoc r) = Some b /\ contains b r)
                                            (fun m0 a m1 -> exists b. m0=m1 /\ blockAtLoc m0 (refLoc r) = Some b /\ sel b r == a)

(**
open List
let sids (m : smem) = map fst (st m)

type notIn  (#a:Type) (e : a) (l : list a) : Tot Type  = a


assume val newStackFrame:  unit -> ST unit
                                    (fun m -> True)
                                    (fun m0 a m1 -> exists s1. (isTop s1 (st m1)) /\ notIn (sid s1) (sids m0) /\ btail (st m1) = (st m0) ) (* and (fst s1) is empty*)
                                    *)
(*
assume val read:  #a:Type -> r:ref a -> STATE a
                                         (fun 'p h -> 'p (sel h r) h)
                                         (fun 'p h -> 'p (sel h r) h)

assume val write:  #a:Type -> r:ref a -> v:a -> Prims.ST unit
                                                 (fun h -> True)
                                                 (fun h0 x h1 -> h1==upd h0 r v)

assume val op_ColonEquals:  #a:Type -> r:ref a -> v:a -> Prims.ST unit
                                                 (fun h -> True)
                                                 (fun h0 x h1 -> h1==upd h0 r v)


assume val get: unit -> ST heap (fun h -> True) (fun h0 h h1 -> h0==h1 /\ h=h1) (modifies no_refs)
*)

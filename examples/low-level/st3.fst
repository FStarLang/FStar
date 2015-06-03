(*--build-config
    options:--admit_fsi Set;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst stack.fst
  --*)

module StructuredMem
open Heap
open Stack
open Set
open Prims

type sidt = nat


(* should we way that the stack ids are unique and contained in the list of sidts : {contains (map snd (fst p)) (snd p)}*)
type memStack = x:((Stack (sidt * heap)) * (list sidt))
(* should we also include sizes of refs in order to enable reasoninag about memory usage of programs?*)
(* what is the size of programs ?*)
type smem = heap * memStack

(*rename heap to memblock, and then hp to heap*)
let hp (s : smem) = fst s

val st : smem -> Tot (Stack (sidt * heap))
let st (s : smem) = fst (snd s)

let sid (s : (sidt * heap)) = fst s

val topst : (s:smem{ (snonempty (st s)) == true}) -> Tot  (sidt * heap)
let topst ss = (top (st ss))

val topstb : (s:smem{ (snonempty (st s)) == true}) ->  Tot heap
let topstb ss = snd (topst ss)

val topstid : (s:smem{ (snonempty (st s)) == true}) ->  Tot sidt
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


type allocateInBlock (#a:Type) (r: ref a) (h0 : heap) (h1 : heap) (init : a)   = not(contains h0 r) /\ contains h1 r /\  h1 == upd h0 r init



assume val halloc:  #a:Type -> init:a -> ST (ref a)
                                         (fun m -> True)
                                         (fun m0 r m1 -> allocateInBlock r (hp m0)  (hp m1) init /\ (st m0 == st m1) /\ refLoc r == InHeap)

assume val salloc:  #a:Type -> init:a -> ST (ref a)
     (fun m -> (snonempty (st m) == true))
     (fun m0 r m1 ->
          (snonempty (st m0) == true) /\ (snonempty (st m1)) == true
          /\ allocateInBlock r (topstb m0) (topstb m0) init
          /\ refLoc r == InStack (topstid m0) /\ (topstid m0 = topstid m1)
          /\ stail (st m0) == stail (st m1) /\ (hp m0) == hp m1)

(*HELP : how to write this:
val refExistsInMem : #a:Type -> (ref a) -> smem ->  Tot Type
let refExistsInMem (#a:Type) (r:ref a) (m:smem) =
match (blockAtLoc m (refLoc r)) with
          | Some b -> contains b r
          | None -> false
*)

val refExistsInMem : #a:Type -> (ref a) -> smem ->  Tot bool
let refExistsInMem (#a:Type) (r:ref a) (m:smem) =
match (blockAtLoc m (refLoc r)) with
          | Some b -> contains b r
          | None -> false

(* BUG: sel should not always return something, it would be tricky to implement it.
  what prevents me from creating a ref of an empty type?
*)
val loopkupRef : #a:Type -> (ref a) -> smem ->  Tot (option a)
let loopkupRef (#a:Type) (r:ref a) (m:smem) =
match (blockAtLoc m (refLoc r)) with
          | Some b -> Some (sel b r)
          | None -> None

assume val read:  #a:Type -> r:(ref a) -> ST a
	  (fun m -> (refExistsInMem r m) == true)
    (fun m0 a m1 -> m0=m1 /\ loopkupRef r m0 = Some a)


val lmap : #a:Type -> #b:Type -> (a -> Tot b) -> (list a) -> Tot (list b)
let rec lmap f l =
match l with
| nil -> []
| h::tl -> (f h)::(lmap f tl)


val sids : smem -> Tot (list sidt)
let sids (m : smem) = lmap fst (st m)

assume val inList : sidt -> (list sidt) -> Tot bool

assume val newStackFrame:  unit -> ST unit
    (fun m -> True)
    (fun m0 a m1 -> stail (st m1) = (st m0) /\ (snonempty (st m1) == true) /\ ((inList (topstid m1) (sids m0)) == false) /\ (topstb m1) = emp)


(*
assume val write:  #a:Type -> r:(ref a) -> ST unit
	    (fun m -> (refExistsInMem r m) == true)
      (fun m0 a m1 -> m0=m1 /\ loopkupRef r m0 = Some a)
*)

(*


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

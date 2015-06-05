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
type memStackAux = ((Stack (sidt * heap)) * (list sidt))

val wellFormed : memStackAux -> Tot bool
let wellFormed x =
let stids = (mapT fst (fst x)) in
  let idhistory = (snd x) in
  (lsubset stids idhistory) && (noRepeats stids)

(* should we way that the stack ids are unique and contained in the list of sidts : {contains (map snd (fst p)) (snd p)}*)
type memStack = x:memStackAux{wellFormed x}


(* should we also include sizes of refs in order to enable reasoninag about memory usage of programs?*)
(* what is the size of programs ?*)
type smem = heap * memStack


(*rename heap to memblock, and then hp to heap*)
let hp (s : smem) = fst s

val st : smem -> Tot (Stack (sidt * heap))
let st (s : smem) = fst (snd s)

val sids : smem -> Tot (list sidt)
let sids (m : smem) = mapT fst (st m)

val idHistory : smem -> Tot (list sidt)
let idHistory (s : smem) = snd (snd s)

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

effect SST (a:Type) (pre:Pre) (post: (smem -> Post a)) =
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



assume val halloc:  #a:Type -> init:a -> SST (ref a)
                                         (fun m -> True)
                                         (fun m0 r m1 -> allocateInBlock r (hp m0)  (hp m1) init /\ (st m0 == st m1) /\ refLoc r == InHeap)

assume val salloc:  #a:Type -> init:a -> SST (ref a)
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

assume val read:  #a:Type -> r:(ref a) -> SST a
	  (fun m -> (refExistsInMem r m) == true)
    (fun m0 a m1 -> m0=m1 /\ loopkupRef r m0 = Some a)



assume val newStackFrame:  unit -> SST unit
    (fun m -> True)
    (fun m0 a m1 -> stail (st m1) = (st m0) /\ (isNonEmpty (st m1)) /\ (notIn (topstid m1) (sids m0)) /\ (topstb m1) = emp)



(* are there associative maps in FStar? *)
(*  proof by computation *)


val writeMemStack : #a:Type -> (ref a) -> (Stack (sidt * heap)) -> sidt -> a -> Tot (Stack (sidt * heap))
let rec writeMemStack r ms s v =
match ms with
| Nil -> Nil
| h::tl ->
  (if (fst h = s) then ((fst h, (upd (snd h) r v))::tl) else h::(writeMemStack r tl s v))

val writeMemStackLem : #a:Type -> r:(ref a) -> ms:(Stack (sidt * heap))
  -> s:sidt -> v:a
  -> Lemma ((mapT fst ms) = (mapT fst (writeMemStack r ms s v)))
          (* [SMTPat (writeMemStack r ms s v)] *)
let rec writeMemStackLem r ms s v =
match ms with
| Nil -> ()
| h::tl ->   if (fst h = s) then () else (writeMemStackLem r tl s v)


val writeMemStackLem2 : #a:Type -> r:(ref a)
  -> his : (list sidt)
  -> ms:(Stack (sidt * heap))
  -> s:sidt -> v:a
  -> Lemma
      (requires (wellFormed (ms,his)))
      (ensures (wellFormed ((writeMemStack r ms s v),his)))
      [SMTPat (writeMemStack r ms s v)]
let writeMemStackLem2 r his ms s v = admit ()
(* ((writeMemStackLem r ms s v)) *)

(* what is the analog of transport / eq_ind?*)


val writeMemAux : #a:Type -> (ref a) -> m:smem -> a -> Tot smem
let writeMemAux r m v =
  match (refLoc r) with
  | InHeap -> ((upd (hp m) r v), snd m)
  | InStack s -> ((hp m), ((writeMemStack r (st m) s v), idHistory m))



assume val write:  #a:Type -> r:(ref a) -> v:a ->
  SST unit
	    (fun m -> (refExistsInMem r m) == true)
      (fun m0 a m1 -> (writeMemAux r m0 v) ==  m1)



kind SSTPost (a:Type) = STPost_h smem a

sub_effect
  DIV   ~> StSTATE = fun (a:Type) (wp:PureWP a) (p : SSTPost a) (h:smem) -> wp (fun a -> p a h)

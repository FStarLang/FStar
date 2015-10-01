(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:ext.fst set.fsi heap.fst st.fst all.fst list.fst
      stack.fst listset.fst ghost.fst located.fst lref.fst
  --*)

(* Note: we need the definitions of the functions from the [List]
   module to reason about them, so not --admit_fsi for [FStar.List]. *)

module Regions

(** An axiomatization of regions in F* *)

open FStar.Set
open FStar.List
open FStar.Ghost

open ListSet
open Located
open Lref

(** A region, taken individually, behaves just like a heap of its own. Beware!
    This type is defined in [Lref] (it is *not* the standard FStar heap type). *)
type region = heap


(* Recall that the [Located] module defines [rid], the type of region-ids. In
   our axiomatization of regions, we carry around a stack of regions where each
   region is tagged with an [rid]. This axiomatization can be realized with two
   different models:
   - one where [rid]s are globally unique throughout the entire program
     execution, and
   - one where [rid]s may be re-used.
   The client code cannot assume one model or another (we're providing the
   client with a weaker model than, say, one that guarantees that [rid]s are
   never reused). This is similar to [ST] where the client cannot assume either
   that memory locations will never be re-used. *)
type regionStack = Stack.stack (rid * region)

(* The naming convention is as follows: functions that operate on the "stack"
   part of the memory end with [St], while functions that operate on the [smem]
   type below end with [Mem]. *)
val ridsSt : regionStack -> Tot (list rid)
let ridsSt ms = mapT fst ms

val wellFormed : regionStack -> Tot bool
let wellFormed ms = noRepeats (ridsSt ms)

(* A well-formed region stack is one where no [rid] appears twice. *)
type wfRegionStack= x:regionStack{wellFormed x}


(* The type of our memory: a garbage-collected heap along with a
   custom-managed stack of regions. *)
type smem = heap * wfRegionStack

(* A series of helpers to work with the [smem] type. *)
val hp : smem -> Tot heap
let hp = fst

val st : smem -> Tot wfRegionStack
let st = snd

val tail : smem -> Tot smem
let tail (m : smem) =
  hp m, Stack.tail (st m)

val rids : smem -> Tot (list rid)
let rids (m : smem) = ridsSt (st m)

val topRegionAndId : s:smem{Stack.isNonEmpty (st s)} -> Tot (rid * region)
let topRegionAndId ss = Stack.top (st ss)

val topRegion : s:smem{Stack.isNonEmpty (st s)} -> Tot region
let topRegion ss = snd (topRegionAndId ss)

val topRegionId : s:smem{Stack.isNonEmpty (st s)} ->  Tot rid
let topRegionId ss = fst (topRegionAndId ss)

val refLoc : #a:Type -> lref a -> Tot regionLoc
let refLoc r = regionOf r


(* Find a region by [rid]. *)
val regionById : rid  -> Stack.stack (rid * region) -> Tot (option region)
let rec regionById id sp =
  match sp with
  | Nil -> None
  | h::tl -> if id = fst h then Some (snd h) else regionById id tl

(* Find a region by [regionLoc] (see [located.fst]). *)
val regionByLoc : smem -> regionLoc -> Tot (option region)
let regionByLoc m rl =
  match rl with
  | InHeap -> Some (hp m)
  | InStack id -> regionById id (st m)

(* A wrapper around [upd] (from [lref.fst]) that reverses the order of
   the arguments, hence making it better suited to partial
   application. *)
val writeInRegion : #a:Type -> r:lref a -> v:a -> region -> Tot region
let writeInRegion r v mb = upd mb r v

(* Apply a function on a specific region in stack, leaving the rest
   untouched. Typically used with a partial application of the
   combinator above. *)
val updateRegionById : (region -> Tot region)
  -> rid
  -> ms:regionStack
  -> Tot (r:regionStack{ridsSt r = ridsSt ms})
let rec updateRegionById f s ms=
  match ms with
  | [] -> []
  | h::tl ->
      if fst h = s then
        (fst h, f (snd h))::tl
       else
         h::updateRegionById f s tl

(* Write a new value in a reference that's in a given region id. *)
val writeInRegionStack : #a:Type -> lref a -> s:regionStack -> rid -> a -> Tot (r:regionStack{ridsSt r = ridsSt s})
let rec writeInRegionStack r ms s v = updateRegionById (writeInRegion r v) s ms


(** A series of lemmas about updating the stack of regions. *)

(* Calling [updateByRegionId] does not change the region-ids. *)
val updateRegionSameIds :
    f:(region -> Tot region) -> s:rid -> ms:regionStack
  -> Lemma (ensures (ridsSt ms = ridsSt (updateRegionById f s ms)))
let rec updateRegionSameIds f s ms =
  match ms with
  | Nil -> ()
  | h::tl -> if fst h = s then () else updateRegionSameIds f s tl


(* Calling [updateByRegionId] preserves the well-formedness of the region
   stack. *)
val updateRegionWellFormed :
 f:(region -> Tot region) -> s:rid -> ms:regionStack
  -> Lemma
      (requires (wellFormed ms))
      (ensures (wellFormed (updateRegionById f s ms)))
let updateRegionWellFormed  f s ms = updateRegionSameIds f s ms


(* Updating one of the regions does not change the region-ids. *)
val writeRegionStackSameIds : #a:Type -> r:(lref a) -> ms:(regionStack)
  -> s:rid -> v:a
  -> Lemma (ensures (ridsSt ms = ridsSt (writeInRegionStack r ms s v)))
let writeRegionStackSameIds r ms s v = updateRegionSameIds (writeInRegion r v) s ms


(* Updating one the regions perserves the well-formedness of the region stack. *)
val writeRegionStackWellFormed : #a:Type -> r:(lref a)
  -> ms:(regionStack)
  -> s:rid -> v:a
  -> Lemma
      (requires (wellFormed (ms)))
      (ensures (wellFormed (writeInRegionStack r ms s v)))
      [SMTPat (writeInRegionStack r ms s v)]
let writeRegionStackWellFormed r ms s v = (updateRegionWellFormed (writeInRegion r v) s ms)


(* Does a reference belong to the region with the given id? *)
val refExistsInStack : #a:Type -> lref a
  -> id:rid -> regionStack -> Tot bool
let rec refExistsInStack r id ms =
  match ms with
  | [] -> false
  | h::tl -> if fst h = id then contains (snd h) r else refExistsInStack r id tl


val refExistsInStackId : #a:Type -> r:(lref a)
  -> id:rid -> ms:(regionStack)
  -> Lemma (requires (refExistsInStack r id ms))
          (ensures (memT id (ridsSt ms)))
let rec refExistsInStackId r id ms =
  match ms with
  | [] -> ()
  | h::tl -> if (fst h=id) then () else (refExistsInStackId r id tl)

val memIdUniq:  h:(rid * region) -> tl:regionStack
  -> Lemma (requires (wellFormed (h::tl)))
        (ensures (notIn (fst h) (ridsSt tl)))
let memIdUniq h tl = ()


val refExistsInStackTail : #a:Type -> r:(lref a)
  -> id:rid -> ms:wfRegionStack  -> Lemma (requires (refExistsInStack r id (Stack.tail ms)))
          (ensures  (refExistsInStack r id ms))
          [SMTPat (refExistsInStack r id (Stack.tail ms))]
let refExistsInStackTail r id ms = (refExistsInStackId r id (Stack.tail ms))


val liveRef : #a:Type -> (lref a) -> smem ->  Tot bool
let liveRef (#a:Type) (r:lref a) (m:smem) =
  match (refLoc r) with
  | InHeap -> contains (hp m) r
  | InStack id -> refExistsInStack r id (st m)


val writeRegionStackExists : #a:Type -> #b:Type -> rw:(lref a) -> r: (lref b)
  -> ms:(regionStack)
  -> id:rid -> idw:rid -> v:a
  -> Lemma
      (requires (refExistsInStack r id ms))
      (ensures (refExistsInStack r id (writeInRegionStack rw ms idw v)))
      [SMTPat (writeInRegionStack rw ms id v)]
let rec writeRegionStackExists rw r ms id idw v =
  match ms with
  | Nil -> ()
  | h::tl ->   if (fst h = id) then () else ((writeRegionStackExists rw r tl id idw v))


val writeMemAux : #a:Type -> (lref a) -> m:smem -> a -> Tot (r:smem{rids r = rids m})
let writeMemAux r m v =
  match (refLoc r) with
  | InHeap -> ((upd (hp m) r v), snd m)
  | InStack id -> ( (hp m), (writeInRegionStack r (st m) id v) )



val writeMemAuxPreservesExists :  #a:Type -> #b:Type ->
  rw:lref a -> r:lref b -> m:smem -> v:a ->
Lemma (requires (liveRef r m))
      (ensures (liveRef r (writeMemAux rw m v)))
      [SMTPat (writeMemAux rw m v)]
let writeMemAuxPreservesExists rw r m v =
match (refLoc r) with
| InHeap -> ()
| InStack id ->
    match (refLoc rw) with
    | InHeap -> ()
    | InStack idw ->  (writeRegionStackExists rw r (st m) id idw v)


val writeMemAuxPreservesIdsSt :  #a:Type -> rw:lref a  -> m:smem -> v:a ->
Lemma (requires (True)) (ensures (rids m = rids (writeMemAux rw m v)))
 [SMTPat (writeMemAux rw m v)]

let writeMemAuxPreservesIdsSt rw m v =
match (refLoc rw) with
| InHeap -> ()
| InStack id ->  (writeRegionStackSameIds rw (st m) id v)


(*
val writeMemAuxPreservesStail :  #a:Type -> r:(lref a) -> m:smem -> v:a ->
Lemma (requires (is_InStack (refLoc r)))
  (ensures tail m = tail (writeMemAux r m v))
let rec writeMemAuxPreservesStail r m v =  ()
*)

val lookupRefStack : #a:Type -> r:(lref a) -> id:rid -> ms:(regionStack){refExistsInStack r id ms}  ->  Tot a
let rec lookupRefStack r id ms =
match ms with
| h::tl ->
    if (fst h = id) then  sel (snd h) r else (lookupRefStack r id tl)


(* it is surprising that sel always returns something; It might be tricky to implement it.
   What prevents me from creating a lref of an empty type? Perhaps it is impossible to create a member
   of the type (lref False) . For example, the memory allocation operator, which creates a new (lref 'a)
   requires an initial value of type 'a
*)
val lookupRef : #a:Type -> r:(lref a) -> m:smem{(liveRef r m) == true} ->  Tot a
let lookupRef r m =
match (refLoc r) with
| InHeap -> (sel (hp m) r)
| InStack id -> lookupRefStack r id (st m)


type ifthenelseT (b:Type) (tc : Type) (fc: Type) =
 (b ==>  tc) /\ ((~b) ==> fc )

val readAfterWriteStack :
  #a:Type  -> #b:Type -> rw:(lref a) -> r:(lref b) -> v:a -> id:rid -> idw:rid -> m:(regionStack) ->
  Lemma (requires (refExistsInStack r id m))
        (ensures ((refExistsInStack r id m)
            /\ ifthenelseT (r==rw /\ id=idw)
                (lookupRefStack r id (writeInRegionStack rw m idw v) == v)
                (lookupRefStack r id (writeInRegionStack rw m idw v) = (lookupRefStack r id m))))
let rec readAfterWriteStack rw r v id idw m =
match m with
| [] -> ()
| h::tl ->
  if (fst h = idw)
    then ()
    else (if (fst h=id)
              then ()
              else ((readAfterWriteStack rw r v id idw tl)))

(*perhaps this specialization is not requires anymore*)
val readAfterWriteStackSameType :
  #a:Type -> rw:(lref a) -> r:(lref a) -> v:a -> id:rid -> idw:rid -> m:(regionStack) ->
  Lemma (requires (refExistsInStack r id m))
        (ensures ((refExistsInStack r id m)
            /\ lookupRefStack r id (writeInRegionStack rw m idw v) = (if (r=rw && id=idw) then v else (lookupRefStack r id m))))
let readAfterWriteStackSameType rw r v id idw m = readAfterWriteStack rw r v id idw m

val readAfterWrite : #a:Type -> #b:Type ->  rw:(lref a) -> r:(lref b) -> v:a -> m:smem ->
  Lemma (requires (liveRef r m))
        (ensures (liveRef r m)
        /\ ifthenelseT (r==rw)
            (lookupRef r (writeMemAux rw m v) == v)
            (lookupRef r (writeMemAux rw m v) = (lookupRef r m)))
let readAfterWrite rw r v m =
match (refLoc r) with
| InHeap -> ()
| InStack id ->
  match (refLoc rw) with
  | InHeap -> ()
  | InStack idw -> (readAfterWriteStack rw r v id idw (st m))

(*Again, F*  does not seem to unfold ifthenelseT in the above. So, it seems
necessary to provide the 2 specializations below as an SMTPat,
instead of just the above lemma *)
val readAfterWriteTrue : #a:Type -> #b:Type ->  rw:(lref a) -> r:(lref b) -> v:a -> m:smem ->
  Lemma (requires (liveRef r m /\ r==rw))
        (ensures (liveRef r m) /\
            (lookupRef r (writeMemAux rw m v) == v))
        [SMTPat (writeMemAux rw m v)]
let readAfterWriteTrue rw r v m = readAfterWrite rw r v m


val readAfterWriteFalse : #a:Type -> #b:Type ->  rw:(lref a) -> r:(lref b) -> v:a -> m:smem ->
  Lemma (requires (liveRef r m /\ r=!=rw))
        (ensures (liveRef r m) /\
        (lookupRef r (writeMemAux rw m v) = (lookupRef r m)))
        [SMTPat (writeMemAux rw m v)]
let readAfterWriteFalse rw r v m = readAfterWrite rw r v m


(*perhaps this specialization is not requires anymore*)
val readAfterWriteSameType : #a:Type -> rw:(lref a) -> r:(lref a) -> v:a -> m:smem ->
  Lemma (requires (liveRef r m))
        (ensures (liveRef r m)
            /\ lookupRef r (writeMemAux rw m v) = (if (r=rw) then v else (lookupRef r m)))
let readAfterWriteSameType rw r v m = readAfterWrite rw r v m


val liveRefTail : #a:Type -> r:(lref a) -> m:smem ->
  Lemma (requires (liveRef r (tail m)))
        (ensures (liveRef r (m)))
        [SMTPat (liveRef r (tail m))]
let liveRefTail r m =
match (refLoc r) with
| InHeap -> ()
| InStack id -> (refExistsInStackTail r id (st m))

val lookupRefStackTail
  : #a:Type -> r:(lref a) -> id:rid -> m:wfRegionStack    ->  Lemma
   (requires (refExistsInStack r id (Stack.tail m)))
    (ensures ((refExistsInStack r id (Stack.tail m)) /\ lookupRefStack r id m
        = lookupRefStack r id (Stack.tail m)))
let lookupRefStackTail r id ms = (refExistsInStackId r id (Stack.tail ms))


val readTailRef : #a:Type -> r:(lref a) -> m:smem ->
  Lemma (requires (liveRef r (tail m)))
        (ensures (liveRef r (tail m))
            /\ lookupRef r m =  lookupRef r (tail m))
            [SMTPat (liveRef r (tail m))]
let readTailRef r m =
match (refLoc r) with
| InHeap -> ()
| InStack id -> (lookupRefStackTail r id (st m))


val writeStackTail
  : #a:Type -> r:(lref a) -> id:rid -> v:a -> m:wfRegionStack    ->  Lemma
      (requires (refExistsInStack r id (Stack.tail m)))
      (ensures (Stack.tail (writeInRegionStack r m id v)
                    = writeInRegionStack r (Stack.tail m) id v))
let writeStackTail r id v ms = (refExistsInStackId r id (Stack.tail ms))

val writeTailRef : #a:Type -> r:(lref a) -> m:smem -> v:a ->
  Lemma (requires (liveRef r (tail m)))
        (ensures (liveRef r (tail m))
            /\ tail (writeMemAux r m v) =  writeMemAux r (tail m) v)
            [SMTPat (liveRef r (tail m))]
let writeTailRef r m v =
match (refLoc r) with
| InHeap -> ()
| InStack id -> (writeStackTail r id v (st m))

(* The location of a lref (say r) is refLoc r, and is independent of the
   currrent state of the memory. So the absolute location of a reference is
   by definition preserved by all memory operations.

   However, in most correctness proofs, what matters is the relative position
   w.r.t the top of the stack e.g.
   whether the reference is in the tail of memory.
   There are some memory operations that do not preserve relative position,
   e.g. pushRegion.
   However, most sane program blocks will preserve it. So far,
   preserving stack ids is a definition of sanity
   *)

val liveRefSTailRids : #a:Type -> r:(lref a) -> id:rid  -> m0:wfRegionStack-> m1:wfRegionStack  -> Lemma
   (requires (ridsSt m0 = ridsSt m1
            /\ refExistsInStack r id (Stack.tail m0)
            (*/\ refExistsInStack r id m0*)
            /\ refExistsInStack r id m1))
   (ensures refExistsInStack r id (Stack.tail m1))
let liveRefSTailRids r id m0 m1 =
(refExistsInStackId r id (Stack.tail m0))


val liveRefTailRids : #a:Type -> r:(lref a) -> m0:smem -> m1:smem -> Lemma
  (requires (rids m0 = rids m1 /\ liveRef r (tail m0) /\ liveRef r m1))
  (ensures liveRef r (tail m1))
  [SMTPat (rids m0 = rids m1)]
let liveRefTailRids r m0 m1 =
match (refLoc r) with
| InHeap -> ()
| InStack id -> (liveRefSTailRids r id (st m0) (st m1))



(** modifiesOnly and lemmas about it*)

(** cannot just uses ST.modifies. That was on heap; has to be lifted to smem.
Also, why does it's definition have to be so procedural, unlike the more declarative one below?
*)
type canModify  (m0 : smem)  (m1: smem) (rs: modset ) =
  forall (a:Type) (r: lref a).
      liveRef r m0
      ==> (~(Set.mem (Ref r) (reveal rs)))
      ==> (liveRef r m1 /\ (lookupRef r m0 = lookupRef r m1))


type  mreads (#a:Type) (r: lref a) (v:a) (m:smem) = liveRef r m /\ lookupRef r m = v

(*lemmas needed for automatic inference*)
val canModifyNone : m:smem -> Lemma (canModify m m (hide empty))
let canModifyNone m = ()

val canModifyWrite : #a:Type -> r:(lref a) -> v:a -> m:smem
  -> Lemma (canModify m (writeMemAux r m v) (only  r))
let canModifyWrite r v m = ()

type mStackNonEmpty (m:smem) = b2t (Stack.isNonEmpty (st m))



type allocatedInRegion (#a:Type) (r: lref a) (h0 : region) (h1 : region) (init : a)  =
  not (contains h0 r) /\ contains h1 r /\  h1 == upd h0 r init

val allocateInTopR: #a:Type -> r:lref a -> init:a -> m0:smem{Stack.isNonEmpty (st m0) /\
                                                             not (contains (topRegion m0) r)}
                    -> Tot smem
let allocateInTopR r init m0 =
    hp m0, (topRegionId m0, upd (topRegion m0) r init)::Stack.tail (st m0)


(* liveness for arbitrary located data. It merely says that the stack id valid
   This could be a much simpler definition for liveRef, if we agree to never (manually) free data.*)
val liveLoc : #a:Type -> (located a) -> smem ->  Tot bool
let liveLoc v m =
  match (regionOf v) with
  | InHeap -> true
  | InStack id -> memT id  (rids m)


(** XXX some commented-out lemmas (?) by Abhishek. *)

(*val freeInRegionStackSameIDs : #a:Type -> r:(lref a) -> ms:(regionStack)
  -> s:rid
  -> Lemma (ensures ((ridsSt ms) = (ridsSt (freeInRegionStack r ms s))))
let freeInRegionStackSameIDs r ms s = (updateRegionSameIds (freeRefInBlock r) s ms)

val freeInRegionStackWellFormed : #a:Type -> r:(lref a)
  -> ms:(regionStack)
  -> s:rid
  -> Lemma
      (requires (wellFormed (ms)))
      (ensures (wellFormed (freeInRegionStack r ms s)))
      [SMTPat (freeInRegionStack r ms s)]
let freeInRegionStackWellFormed r ms s = (updateRegionWellFormed (freeRefInBlock r) s ms)*)


(*
val writeRegionStackSameStail : #a:Type -> r:(lref a) -> ms:(regionStack)
  -> s:rid -> v:a
  -> Lemma (ensures ((stail ms) = (stail (writeInRegionStack r ms s v))))
         (*  [SMTPat (writeRegionStack r ms s v)] *)
let rec writeRegionStackSameStail r ms s v = ()
*)


(*val freeMemAux : #a:Type -> (lref a) -> m:smem  -> Tot smem
let freeMemAux r m =
  match (refLoc r) with
  | InHeap -> ((freeRefInBlock r (hp m)), snd m)
  | InStack s -> ((hp m), ((freeInRegionStack r (st m) s)))*)


(*val canModifySalloc : #a:Type -> r:(lref a) -> v:a -> m:smem
  -> Lemma (canModify m (writeMemAux r m v) (singleton (Ref r)))
let canModifyWrite r v m = ()*)

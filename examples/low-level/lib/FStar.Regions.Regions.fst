(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Ghost.fst FStar.List.Tot.fst FStar.Stack.fst FStar.Regions.Located.fst FStar.Regions.Heap.fst
  --*)

(* Note: we need the definitions of the functions from the [List]
   module to reason about them, so not --admit_fsi for [FStar.List]. *)

module FStar.Regions.Regions

(** An axiomatization of regions in F*. **)

open FStar.Set
open FStar.List.Tot
open FStar.Ghost
open FStar.Regions.Located
open FStar.Regions.Heap

(** A region, taken individually, behaves just like a heap of its own. Beware!
    This type is defined in [FStar.Regions.Heap] (it is *not* the standard FStar heap type). *)
type region = heap


(* Recall that the [FStar.Regions.Located] module defines [rid], the type of region-ids. In
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
let ridsSt ms = map fst ms

val wellFormed : regionStack -> Tot bool
let wellFormed ms = noRepeats (ridsSt ms)

(* A well-formed region stack is one where no [rid] appears twice. *)
type wfRegionStack= x:regionStack{wellFormed x}


(* The type of our memory: a garbage-collected heap along with a
   custom-managed stack of regions. JP: better name here? *)
type smem = heap * wfRegionStack

(* A series of helpers to work with the [smem] type. *)
val hp : smem -> Tot heap
let hp x = fst x

val st : smem -> Tot wfRegionStack
let st x = snd x

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

(* The specification-level [:=] operator for writing into a region with a
   specific id. JP: better name here? *)
val writeInRegionStack : #a:Type -> lref a -> s:regionStack -> rid -> a -> Tot (r:regionStack{ridsSt r = ridsSt s})
let writeInRegionStack r ms s v = updateRegionById (writeInRegion r v) s ms


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
let writeRegionStackWellFormed r ms s v = updateRegionWellFormed (writeInRegion r v) s ms


(* Does a reference belong to the region with the given id? *)
val refIsLiveInStack : #a:Type -> lref a
  -> id:rid -> regionStack -> Tot bool
let rec refIsLiveInStack r id ms =
  match ms with
  | [] -> false
  | h::tl -> if fst h = id then contains (snd h) r else refIsLiveInStack r id tl


(* If [refIsLiveInStack r rid ...], then it must be the case that [rid] is one
   of the current region-ids. *)
val refIsLiveInStackId : #a:Type -> r:(lref a)
  -> id:rid -> ms:regionStack
  -> Lemma (requires (refIsLiveInStack r id ms))
          (ensures (mem id (ridsSt ms)))
let rec refIsLiveInStackId r id ms =
  match ms with
  | [] -> ()
  | h::tl -> if fst h = id then () else refIsLiveInStackId r id tl


(* The [rid] at the top of the region stack is not found in the tail. *)
val memIdUniq:  h:(rid * region) -> tl:regionStack
  -> Lemma (requires (wellFormed (h::tl)))
        (ensures (not (mem (fst h) (ridsSt tl))))
let memIdUniq h tl = ()


(* If a reference is found in the tail of the region stack, then it is found in
   the region stack. *)
val refIsLiveInStackTail : #a:Type -> r:lref a
  -> id:rid -> ms:wfRegionStack  -> Lemma (requires (refIsLiveInStack r id (Stack.tail ms)))
          (ensures  (refIsLiveInStack r id ms))
          [SMTPat (refIsLiveInStack r id (Stack.tail ms))]
let refIsLiveInStackTail r id ms = refIsLiveInStackId r id (Stack.tail ms)


(* A predicate to assert the liveness of a reference regardless of whether it's
   in the region stack or in the garbage-collected heap. *)
val refIsLive : #a:Type -> lref a -> smem ->  Tot bool
let refIsLive r m =
  match regionOf r with
  | InHeap -> contains (hp m) r
  | InStack id -> refIsLiveInStack r id (st m)


val writeInStackPreservesLiveness : #a:Type -> #b:Type -> rw:lref a -> r:lref b
  -> ms:regionStack
  -> idw:rid -> id:rid -> v:a
  -> Lemma
      (requires (refIsLiveInStack r id ms))
      (ensures (refIsLiveInStack r id (writeInRegionStack rw ms idw v)))
      [SMTPat (refIsLiveInStack r id (writeInRegionStack rw ms idw v))]
let rec writeInStackPreservesLiveness rw r ms idw id v =
  match ms with
  | Nil -> ()
  | h::tl -> if fst h = id then () else writeInStackPreservesLiveness rw r tl idw id v


(* This is specification-level polymorphic [:=] operator that works regardless
   of whether the [lref] is in the heap or in the stack of regions. JP: better
   name here? JP: better name here? *)
val writeMemAux : #a:Type -> lref a -> m:smem -> a -> Tot (r:smem{rids r = rids m})
let writeMemAux r m v =
  match regionOf r with
  | InHeap -> upd (hp m) r v, snd m
  | InStack id -> hp m, writeInRegionStack r (st m) id v


(** A series of lemmas about [writeMemAux]. They don't seem to be used
    elsewhere, but good to have them, I suppose. *)
val writeMemAuxPreservesLiveness :  #a:Type -> #b:Type ->
  rw:lref a -> r:lref b -> m:smem -> v:a ->
Lemma (requires (refIsLive r m))
      (ensures (refIsLive r (writeMemAux rw m v)))
      [SMTPat (refIsLive r (writeMemAux rw m v))]
let writeMemAuxPreservesLiveness rw r m v =
  match regionOf r with
  | InHeap -> ()
  | InStack id ->
      match regionOf rw with
      | InHeap -> ()
      | InStack idw -> writeInStackPreservesLiveness rw r (st m) idw id v

 
val writeMemAuxPreservesRegionIds :  #a:Type -> rw:lref a  -> m:smem -> v:a ->
Lemma (requires (True)) (ensures (rids m = rids (writeMemAux rw m v)))
 [SMTPat (writeMemAux rw m v)]

let writeMemAuxPreservesRegionIds rw m v =
match (regionOf rw) with
| InHeap -> ()
| InStack id ->  (writeRegionStackSameIds rw (st m) id v)


(** The [!] operator, at the specification level, for references that are known
    to be in the stack of regions. JP: better name here? *)
val lookupRefStack : #a:Type -> r:(lref a) -> id:rid -> ms:(regionStack){refIsLiveInStack r id ms}  ->  Tot a
let rec lookupRefStack r id ms =
match ms with
| h::tl ->
    if (fst h = id) then  sel (snd h) r else (lookupRefStack r id tl)


(** The [!] operator, at the specification level, for any located
    reference. Compared to the standard [!] operator, ours comes with an extra
    proof obligation: the reference has to be live, of course. JP: better name
    here? *)
val lookupRef : #a:Type -> r:lref a -> m:smem{refIsLive r m} -> Tot a
let lookupRef r m =
match regionOf r with
| InHeap -> sel (hp m) r
| InStack id -> lookupRefStack r id (st m)


type ifthenelseT (b:Type) (tc : Type) (fc: Type) =
 (b ==>  tc) /\ (~b ==> fc )


(** When writing into [rw] (sitting in region with id [idw]), then reading from
    [r] (sitting in region [id]), then if these parameters match, you read the
    new value, otherwise, you read the previous value. JP: why do we carry
    around [id] and [idw] rather than using [regionOf]? *)
val readAfterWriteStack :
  #a:Type  -> #b:Type -> rw:(lref a) -> r:(lref b) -> v:a -> id:rid -> idw:rid -> m:(regionStack) ->
  Lemma (requires (refIsLiveInStack r id m))
        (ensures (refIsLiveInStack r id m
            /\ ifthenelseT (r==rw /\ id=idw)
                (lookupRefStack r id (writeInRegionStack rw m idw v) == v)
                (lookupRefStack r id (writeInRegionStack rw m idw v) = lookupRefStack r id m)))
let rec readAfterWriteStack rw r v id idw m =
match m with
| [] -> ()
| h::tl ->
  if (fst h = idw)
    then ()
    else (if (fst h=id)
              then ()
              else ((readAfterWriteStack rw r v id idw tl)))


(** Specialization of the lemma above. JP: still a terrible order of
    arguments?!! AA: still needed? *)
val readAfterWriteStackSameType :
  #a:Type -> rw:(lref a) -> r:(lref a) -> v:a -> id:rid -> idw:rid -> m:(regionStack) ->
  Lemma (requires (refIsLiveInStack r id m))
        (ensures ((refIsLiveInStack r id m)
            /\ lookupRefStack r id (writeInRegionStack rw m idw v) = (if (r=rw && id=idw) then v else (lookupRefStack r id m))))
let readAfterWriteStackSameType rw r v id idw m = readAfterWriteStack rw r v id idw m


(** The general lemma for a reference that's located anywhere. *)
val readAfterWrite : #a:Type -> #b:Type ->  rw:lref a -> r:lref b -> v:a -> m:smem ->
  Lemma (requires (refIsLive r m))
        (ensures (refIsLive r m)
        /\ ifthenelseT (r==rw)
            (lookupRef r (writeMemAux rw m v) == v)
            (lookupRef r (writeMemAux rw m v) = lookupRef r m))
let readAfterWrite rw r v m =
  match regionOf r, regionOf rw with
  | InStack id, InStack idw -> readAfterWriteStack rw r v id idw (st m)
  | _ -> ()

(* AA: Again, F* does not seem to unfold ifthenelseT in the above. So, it seems
   necessary to provide the 2 specializations below as an SMTPat, instead of
   just the above lemma *)
val readAfterWriteTrue : #a:Type -> #b:Type ->  rw:lref a -> r:lref b -> v:a -> m:smem ->
  Lemma (requires (refIsLive r m /\ r==rw))
        (ensures (refIsLive r m) /\
            (lookupRef r (writeMemAux rw m v) == v))
        [SMTPat (lookupRef r (writeMemAux rw m v))]
let readAfterWriteTrue rw r v m = readAfterWrite rw r v m


val readAfterWriteFalse : #a:Type -> #b:Type ->  rw:lref a -> r:lref b -> v:a -> m:smem ->
  Lemma (requires (refIsLive r m /\ r=!=rw))
        (ensures (refIsLive r m) /\
        (lookupRef r (writeMemAux rw m v) = (lookupRef r m)))
        [SMTPat (lookupRef r (writeMemAux rw m v))]
let readAfterWriteFalse rw r v m = readAfterWrite rw r v m


(* AA: still needed? *)
val readAfterWriteSameType : #a:Type -> rw:(lref a) -> r:(lref a) -> v:a -> m:smem ->
  Lemma (requires (refIsLive r m))
        (ensures (refIsLive r m)
            /\ lookupRef r (writeMemAux rw m v) = (if (r=rw) then v else (lookupRef r m)))
let readAfterWriteSameType rw r v m = readAfterWrite rw r v m


val refIsLiveTail : #a:Type -> r:lref a -> m:smem ->
  Lemma (requires (refIsLive r (tail m)))
        (ensures (refIsLive r (m)))
        [SMTPat (refIsLive r (tail m))]
let refIsLiveTail r m =
match regionOf r with
| InHeap -> ()
| InStack id -> refIsLiveInStackTail r id (st m)


(* If a reference is live in the tail, then looking it up in the stack of
   regions or in the tail of the stack is the same. *)
val lookupRefStackTail:
  #a:Type -> r:lref a -> id:rid -> m:wfRegionStack -> Lemma
   (requires (refIsLiveInStack r id (Stack.tail m)))
    (ensures (refIsLiveInStack r id (Stack.tail m) /\ lookupRefStack r id m
        = lookupRefStack r id (Stack.tail m)))
let lookupRefStackTail r id ms = refIsLiveInStackId r id (Stack.tail ms)


(* Same thing with the [smem] instead of the [wfRegionStack]. *)
val readTailRef : #a:Type -> r:(lref a) -> m:smem ->
  Lemma (requires (refIsLive r (tail m)))
        (ensures (refIsLive r (tail m))
            /\ lookupRef r m =  lookupRef r (tail m))
            [SMTPat (refIsLive r (tail m))]
let readTailRef r m =
match regionOf r with
| InHeap -> ()
| InStack id -> lookupRefStackTail r id (st m)


(* [Stack.tail] and [writeInRegionStack] commute as long as the reference is
   live in the tail. *)
val writeStackTail
  : #a:Type -> r:(lref a) -> id:rid -> v:a -> m:wfRegionStack    ->  Lemma
      (requires (refIsLiveInStack r id (Stack.tail m)))
      (ensures (Stack.tail (writeInRegionStack r m id v)
                    = writeInRegionStack r (Stack.tail m) id v))
let writeStackTail r id v ms = refIsLiveInStackId r id (Stack.tail ms)

(* [tail] and [writeMemAux] commute as long as the reference is live in the
   tail. *)
val writeTailRef : #a:Type -> r:lref a -> m:smem -> v:a ->
  Lemma (requires (refIsLive r (tail m)))
        (ensures (refIsLive r (tail m))
            /\ tail (writeMemAux r m v) =  writeMemAux r (tail m) v)
            [SMTPat (tail (writeMemAux r m v))]
let writeTailRef r m v =
match (regionOf r) with
| InHeap -> ()
| InStack id -> (writeStackTail r id v (st m))


(* AA: The location of an [lref] (say r) is [regionOf r], and is independent of
   the currrent state of the memory. So the absolute location of a reference is
   by definition preserved by all memory operations.

   However, in most correctness proofs, what matters is the relative position
   w.r.t the top of the stack e.g.  whether the reference is in the tail of
   memory.  There are some memory operations that do not preserve relative
   position, e.g. pushRegion.  However, most sane program blocks will preserve
   it. So far, preserving region ids is a definition of sanity. *)

(* If a reference was live in the tail of the region stack, and the region-ids
   haven't changed, then assuming it still is live (JP: shouldn't this be a
   consequence of "the region-ids haven't changed"?), it must still be in the
   tail. *)
val refIsLiveSTailRids : #a:Type -> r:(lref a) -> id:rid  -> m0:wfRegionStack-> m1:wfRegionStack  -> Lemma
   (requires (ridsSt m0 = ridsSt m1
            /\ refIsLiveInStack r id (Stack.tail m0)
            (*/\ refIsLiveInStack r id m0*)
            /\ refIsLiveInStack r id m1))
   (ensures refIsLiveInStack r id (Stack.tail m1))
let refIsLiveSTailRids r id m0 m1 =
  refIsLiveInStackId r id (Stack.tail m0)


(* Same thing over [smem] *)
val refIsLiveTailRids : #a:Type -> r:(lref a) -> m0:smem -> m1:smem -> Lemma
  (requires (rids m0 = rids m1 /\ refIsLive r (tail m0) /\ refIsLive r m1))
  (ensures refIsLive r (tail m1))
let refIsLiveTailRids r m0 m1 =
  match regionOf r with
  | InHeap -> ()
  | InStack id -> (refIsLiveSTailRids r id (st m0) (st m1))


(* JP: gratuitous name + argument order change? *)
(* AA: the equivalent of [ST.modifies] lifted to our [smem] type. This is a more
   declarative definition. *)
type canModify (m0 : smem) (m1: smem) (rs: modset) =
  forall (a:Type) (r: lref a).
      refIsLive r m0 /\ ~(Set.mem (Ref r) (reveal rs))
      ==> (refIsLive r m1 /\ lookupRef r m0 = lookupRef r m1)


(* The reference [r] is live and contains the value [v] in memory [m]. *)
type contains (#a:Type) (r: lref a) (v:a) (m:smem) = refIsLive r m /\ lookupRef r m = v

(* AA: some lemmas needed for automatic inference. *)
val canModifyNone : m:smem -> Lemma (canModify m m (hide Set.empty))
let canModifyNone m = ()

val canModifyWrite : #a:Type -> r:lref a -> v:a -> m:smem
  -> Lemma (canModify m (writeMemAux r m v) (FStar.Regions.Heap.only r))
let canModifyWrite r v m = ()


type mStackNonEmpty (m:smem) = b2t (Stack.isNonEmpty (st m))

type allocatedInRegion (#a:Type) (r: lref a) (h0 : region) (h1 : region) (init : a)  =
  not (FStar.Regions.Heap.contains h0 r) /\ FStar.Regions.Heap.contains h1 r /\  h1 == upd h0 r init

(* A specification-level modelization of allocating in the top region. *)
val allocateInTopR: #a:Type -> r:lref a -> init:a -> m0:smem{Stack.isNonEmpty (st m0) /\
                                                             not (FStar.Regions.Heap.contains (topRegion m0) r)}
                    -> Tot smem
let allocateInTopR r init m0 =
  hp m0, (topRegionId m0, upd (topRegion m0) r init)::Stack.tail (st m0)


(* JP: I mentioned earlier that we should get "region still live ==> any
   reference in that region still live" for free (since we never manually free data). This
   predicate merely says "the region is still live". If we used that for the
   definition of [refIsLive], then we would get the semantics above. *)
val locIsLive : #a:Type -> located a -> smem -> Tot bool
let locIsLive v m =
  match regionOf v with
  | InHeap -> true
  | InStack id -> mem id (rids m)



// (** XXX some commented-out lemmas (?) by Abhishek. *)

// (*val freeInRegionStackSameIDs : #a:Type -> r:(lref a) -> ms:(regionStack)
//   -> s:rid
//   -> Lemma (ensures ((ridsSt ms) = (ridsSt (freeInRegionStack r ms s))))
// let freeInRegionStackSameIDs r ms s = (updateRegionSameIds (freeRefInBlock r) s ms)

// val freeInRegionStackWellFormed : #a:Type -> r:(lref a)
//   -> ms:(regionStack)
//   -> s:rid
//   -> Lemma
//       (requires (wellFormed (ms)))
//       (ensures (wellFormed (freeInRegionStack r ms s)))
//       [SMTPat (freeInRegionStack r ms s)]
// let freeInRegionStackWellFormed r ms s = (updateRegionWellFormed (freeRefInBlock r) s ms)*)


// (*
// val writeRegionStackSameStail : #a:Type -> r:(lref a) -> ms:(regionStack)
//   -> s:rid -> v:a
//   -> Lemma (ensures ((stail ms) = (stail (writeInRegionStack r ms s v))))
//          (*  [SMTPat (writeRegionStack r ms s v)] *)
// let rec writeRegionStackSameStail r ms s v = ()
// *)


// (*val freeMemAux : #a:Type -> (lref a) -> m:smem  -> Tot smem
// let freeMemAux r m =
//   match (regionOf r) with
//   | InHeap -> ((freeRefInBlock r (hp m)), snd m)
//   | InStack s -> ((hp m), ((freeInRegionStack r (st m) s)))*)


// (*val canModifySalloc : #a:Type -> r:(lref a) -> v:a -> m:smem
//   -> Lemma (canModify m (writeMemAux r m v) (singleton (Ref r)))
// let canModifyWrite r v m = ()*)


// (*
// val writeMemAuxPreservesStail :  #a:Type -> r:(lref a) -> m:smem -> v:a ->
// Lemma (requires (is_InStack (regionOf r)))
//   (ensures tail m = tail (writeMemAux r m v))
// let rec writeMemAuxPreservesStail r m v =  ()
// *)

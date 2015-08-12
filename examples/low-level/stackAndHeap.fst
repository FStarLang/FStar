(*--build-config
    variables:LIB=../../lib;
    variables:MATHS=../maths;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/set.fst $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/list.fst stack.fst listset.fst $LIB/ghost.fst located.fst lref.fst
  --*)

(*     options: --codegen OCaml-experimental --trace_error --debug yes --prn; *)

module StackAndHeap
open Heap open Stack
open Set
open Prims
open List
open ListSet
open Ghost

open Located
open Lref
type region = heap


(* The axiomatization is agnostic
about resuse of memory ids, i.e. it should (provably) have both kind of models.
A client code's correctness/well-typedness cannot depend on stack-ids being reused.
This is actually a strictly weaker assumption, than the older one
where the client can potentially depend on stack ids being never reused.

This is similar to the case of freshness of references in ST.
The axiomatization is agnostic about whether a reference can be reused after it
is freed.
*)
type memStackAux = Stack (sidt * region)

val ssids : memStackAux ->  Tot (list sidt)
let ssids ms = mapT fst ms

val wellFormed : memStackAux -> Tot bool
let wellFormed ms = noRepeats (ssids ms)

type memStack = x:memStackAux{wellFormed x}


type smem = region * memStack

let hp (s : smem) = fst s

val st : smem -> Tot (Stack (sidt * region))
let st (s : smem) = (snd s)

val mtail : smem -> Tot smem
let mtail (s : smem) = (hp s, stail (st s))

val mstail : smem -> Tot ((Stack (sidt * region)))
let mstail (s : smem) = stail (st s)

val sids : smem -> Tot (list sidt)
let sids (m : smem) = ssids (st m)

let sid (s : (sidt * region)) = fst s

val topst : (s:smem{isNonEmpty (st s)}) -> Tot  (sidt * region)
let topst ss = (top (st ss))

val topstb : (s:smem{isNonEmpty (st s)}) ->  Tot region
let topstb ss = snd (topst ss)


val topstid : (s:smem{isNonEmpty (st s)}) ->  Tot sidt
let topstid ss = fst (topst ss)


val refLoc : #a:Type -> lref a -> Tot regionLoc
let refLoc r = regionOf r

new_effect StSTATE = STATE_h smem

val stackBlockAtLoc : sidt  -> (Stack (sidt * region)) -> Tot (option region)
let rec stackBlockAtLoc id sp =
  match sp with
  | Nil -> None
  | h::tl -> if (id=(fst h)) then Some (snd h) else stackBlockAtLoc id tl


val blockAtLoc : smem -> regionLoc  -> Tot (option region)
let blockAtLoc m rl =
match rl with
| InHeap -> Some (hp m)
| InStack id -> stackBlockAtLoc id (st m)

val writeInBlock : #a:Type -> r:(lref a) -> v:a -> region -> Tot region
let writeInBlock r v mb= upd mb r v

val changeStackBlockWithId  : (region -> Tot region)
  -> sidt
  -> (Stack (sidt * region))
        -> Tot (Stack (sidt * region))
let rec changeStackBlockWithId f s ms=
match ms with
| [] -> []
| h::tl ->
  (if (fst h = s) then ((fst h, (f (snd h)))::tl) else h::(changeStackBlockWithId f s tl))

val writeInMemStack : #a:Type -> (lref a) -> (Stack (sidt * region)) -> sidt -> a -> Tot (Stack (sidt * region))
let rec writeInMemStack r ms s v = changeStackBlockWithId (writeInBlock r v) s ms



val changeStackBlockSameIDs :
    f:(region -> Tot region) -> s:sidt -> ms:(Stack (sidt * region))
  -> Lemma (ensures ((ssids ms) = (ssids (changeStackBlockWithId f s ms))))
let rec changeStackBlockSameIDs f s ms =
match ms with
| Nil -> ()
| h::tl ->   if (fst h = s) then () else (changeStackBlockSameIDs f s tl)

val changeStackBlockWellFormed :
 f:(region -> Tot region) -> s:sidt -> ms:(Stack (sidt * region))
  -> Lemma
      (requires (wellFormed ms))
      (ensures (wellFormed (changeStackBlockWithId f s ms)))
let changeStackBlockWellFormed  f s ms = (changeStackBlockSameIDs f s ms)

val writeMemStackSameIDs : #a:Type -> r:(lref a) -> ms:(Stack (sidt * region))
  -> s:sidt -> v:a
  -> Lemma (ensures ((ssids ms) = (ssids (writeInMemStack r ms s v))))
let writeMemStackSameIDs r ms s v = (changeStackBlockSameIDs (writeInBlock r v) s ms)

val writeMemStackWellFormed : #a:Type -> r:(lref a)
  -> ms:(Stack (sidt * region))
  -> s:sidt -> v:a
  -> Lemma
      (requires (wellFormed (ms)))
      (ensures (wellFormed (writeInMemStack r ms s v)))
      [SMTPat (writeInMemStack r ms s v)]
let writeMemStackWellFormed r ms s v = (changeStackBlockWellFormed (writeInBlock r v) s ms)

(*val freeInMemStackSameIDs : #a:Type -> r:(lref a) -> ms:(Stack (sidt * region))
  -> s:sidt
  -> Lemma (ensures ((ssids ms) = (ssids (freeInMemStack r ms s))))
let freeInMemStackSameIDs r ms s = (changeStackBlockSameIDs (freeRefInBlock r) s ms)

val freeInMemStackWellFormed : #a:Type -> r:(lref a)
  -> ms:(Stack (sidt * region))
  -> s:sidt
  -> Lemma
      (requires (wellFormed (ms)))
      (ensures (wellFormed (freeInMemStack r ms s)))
      [SMTPat (freeInMemStack r ms s)]
let freeInMemStackWellFormed r ms s = (changeStackBlockWellFormed (freeRefInBlock r) s ms)*)


(*
val writeMemStackSameStail : #a:Type -> r:(lref a) -> ms:(Stack (sidt * region))
  -> s:sidt -> v:a
  -> Lemma (ensures ((stail ms) = (stail (writeInMemStack r ms s v))))
         (*  [SMTPat (writeMemStack r ms s v)] *)
let rec writeMemStackSameStail r ms s v = ()
*)


val refExistsInStack : #a:Type -> (lref a)
  -> id:sidt -> (Stack (sidt * region)) -> Tot bool
let rec refExistsInStack r id ms =
match ms with
| [] -> false
| h::tl -> if (fst h=id) then (contains (snd h) r) else refExistsInStack r id tl


val refExistsInStackId : #a:Type -> r:(lref a)
  -> id:sidt -> ms:(Stack (sidt * region))
  -> Lemma (requires (refExistsInStack r id ms))
          (ensures (memT id (ssids ms)))
let rec refExistsInStackId r id ms =
match ms with
| [] -> ()
| h::tl -> if (fst h=id) then () else (refExistsInStackId r id tl)

val memIdUniq:  h:(sidt * region) -> tl:memStackAux
  -> Lemma (requires (wellFormed (h::tl)))
        (ensures (notIn (fst h) (ssids tl)))
let memIdUniq h tl = ()


val refExistsInStackTail : #a:Type -> r:(lref a)
  -> id:sidt -> ms:memStack
  -> Lemma (requires (refExistsInStack r id (stail ms)))
          (ensures  (refExistsInStack r id ms))
          [SMTPat (refExistsInStack r id (stail ms))]
let refExistsInStackTail r id ms = (refExistsInStackId r id (stail ms))


val liveRef : #a:Type -> (lref a) -> smem ->  Tot bool
let liveRef (#a:Type) (r:lref a) (m:smem) =
match (refLoc r) with
| InHeap -> contains (hp m) r
| InStack id -> refExistsInStack r id (st m)


val writeMemStackExists : #a:Type -> #b:Type -> rw:(lref a) -> r: (lref b)
  -> ms:(Stack (sidt * region))
  -> id:sidt -> idw:sidt -> v:a
  -> Lemma
      (requires (refExistsInStack r id ms))
      (ensures (refExistsInStack r id (writeInMemStack rw ms idw v)))
      [SMTPat (writeInMemStack rw ms id v)]
let rec writeMemStackExists rw r ms id idw v =
match ms with
| Nil -> ()
| h::tl ->   if (fst h = id) then () else ((writeMemStackExists rw r tl id idw v))


val writeMemAux : #a:Type -> (lref a) -> m:smem -> a -> Tot smem
let writeMemAux r m v =
  match (refLoc r) with
  | InHeap -> ((upd (hp m) r v), snd m)
  | InStack id -> ( (hp m), (writeInMemStack r (st m) id v) )


(*val freeMemAux : #a:Type -> (lref a) -> m:smem  -> Tot smem
let freeMemAux r m =
  match (refLoc r) with
  | InHeap -> ((freeRefInBlock r (hp m)), snd m)
  | InStack s -> ((hp m), ((freeInMemStack r (st m) s)))*)


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
    | InStack idw ->  (writeMemStackExists rw r (st m) id idw v)


val writeMemAuxPreservesSids :  #a:Type -> rw:lref a  -> m:smem -> v:a ->
Lemma (requires (True)) (ensures (sids m = sids (writeMemAux rw m v)))
 [SMTPat (writeMemAux rw m v)]

let writeMemAuxPreservesSids rw m v =
match (refLoc rw) with
| InHeap -> ()
| InStack id ->  (writeMemStackSameIDs rw (st m) id v)


(*
val writeMemAuxPreservesStail :  #a:Type -> r:(lref a) -> m:smem -> v:a ->
Lemma (requires (is_InStack (refLoc r)))
  (ensures mtail m = mtail (writeMemAux r m v))
let rec writeMemAuxPreservesStail r m v =  ()
*)

val loopkupRefStack : #a:Type -> r:(lref a) -> id:sidt -> ms:(Stack (sidt * region)){refExistsInStack r id ms}  ->  Tot a
let rec loopkupRefStack r id ms =
match ms with
| h::tl ->
    if (fst h = id) then  sel (snd h) r else (loopkupRefStack r id tl)


(* it is surprising that sel always returns something; It might be tricky to implement it.
   What prevents me from creating a lref of an empty type? Perhaps it is impossible to create a member
   of the type (lref False) . For example, the memory allocation operator, which creates a new (lref 'a)
   requires an initial value of type 'a
*)
val loopkupRef : #a:Type -> r:(lref a) -> m:smem{(liveRef r m) == true} ->  Tot a
let loopkupRef r m =
match (refLoc r) with
| InHeap -> (sel (hp m) r)
| InStack id -> loopkupRefStack r id (st m)


type ifthenelseT (b:Type) (tc : Type) (fc: Type) =
 (b ==>  tc) /\ ((~b) ==> fc )

val readAfterWriteStack :
  #a:Type  -> #b:Type -> rw:(lref a) -> r:(lref b) -> v:a -> id:sidt -> idw:sidt -> m:(Stack (sidt * region)) ->
  Lemma (requires (refExistsInStack r id m))
        (ensures ((refExistsInStack r id m)
            /\ ifthenelseT (r==rw /\ id=idw)
                (loopkupRefStack r id (writeInMemStack rw m idw v) == v)
                (loopkupRefStack r id (writeInMemStack rw m idw v) = (loopkupRefStack r id m))))
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
  #a:Type -> rw:(lref a) -> r:(lref a) -> v:a -> id:sidt -> idw:sidt -> m:(Stack (sidt * region)) ->
  Lemma (requires (refExistsInStack r id m))
        (ensures ((refExistsInStack r id m)
            /\ loopkupRefStack r id (writeInMemStack rw m idw v) = (if (r=rw && id=idw) then v else (loopkupRefStack r id m))))
let readAfterWriteStackSameType rw r v id idw m = readAfterWriteStack rw r v id idw m

val readAfterWrite : #a:Type -> #b:Type ->  rw:(lref a) -> r:(lref b) -> v:a -> m:smem ->
  Lemma (requires (liveRef r m))
        (ensures (liveRef r m)
        /\ ifthenelseT (r==rw)
            (loopkupRef r (writeMemAux rw m v) == v)
            (loopkupRef r (writeMemAux rw m v) = (loopkupRef r m)))
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
            (loopkupRef r (writeMemAux rw m v) == v))
        [SMTPat (writeMemAux rw m v)]
let readAfterWriteTrue rw r v m = readAfterWrite rw r v m


val readAfterWriteFalse : #a:Type -> #b:Type ->  rw:(lref a) -> r:(lref b) -> v:a -> m:smem ->
  Lemma (requires (liveRef r m /\ r=!=rw))
        (ensures (liveRef r m) /\
        (loopkupRef r (writeMemAux rw m v) = (loopkupRef r m)))
        [SMTPat (writeMemAux rw m v)]
let readAfterWriteFalse rw r v m = readAfterWrite rw r v m


(*perhaps this specialization is not requires anymore*)
val readAfterWriteSameType : #a:Type -> rw:(lref a) -> r:(lref a) -> v:a -> m:smem ->
  Lemma (requires (liveRef r m))
        (ensures (liveRef r m)
            /\ loopkupRef r (writeMemAux rw m v) = (if (r=rw) then v else (loopkupRef r m)))
let readAfterWriteSameType rw r v m = readAfterWrite rw r v m


val liveRefTail : #a:Type -> r:(lref a) -> m:smem ->
  Lemma (requires (liveRef r (mtail m)))
        (ensures (liveRef r (m)))
        [SMTPat (liveRef r (mtail m))]
let liveRefTail r m =
match (refLoc r) with
| InHeap -> ()
| InStack id -> (refExistsInStackTail r id (st m))

val loopkupRefStackTail
  : #a:Type -> r:(lref a) -> id:sidt -> m:memStack
    ->  Lemma
   (requires (refExistsInStack r id (stail m)))
    (ensures ((refExistsInStack r id (stail m)) /\ loopkupRefStack r id m
        = loopkupRefStack r id (stail m)))
let loopkupRefStackTail r id ms = (refExistsInStackId r id (stail ms))


val readTailRef : #a:Type -> r:(lref a) -> m:smem ->
  Lemma (requires (liveRef r (mtail m)))
        (ensures (liveRef r (mtail m))
            /\ loopkupRef r m =  loopkupRef r (mtail m))
            [SMTPat (liveRef r (mtail m))]
let readTailRef r m =
match (refLoc r) with
| InHeap -> ()
| InStack id -> (loopkupRefStackTail r id (st m))


val writeStackTail
  : #a:Type -> r:(lref a) -> id:sidt -> v:a -> m:memStack
    ->  Lemma
      (requires (refExistsInStack r id (stail m)))
      (ensures (stail (writeInMemStack r m id v)
                    = writeInMemStack r (stail m) id v))
let writeStackTail r id v ms = (refExistsInStackId r id (stail ms))

val writeTailRef : #a:Type -> r:(lref a) -> m:smem -> v:a ->
  Lemma (requires (liveRef r (mtail m)))
        (ensures (liveRef r (mtail m))
            /\ mtail (writeMemAux r m v) =  writeMemAux r (mtail m) v)
            [SMTPat (liveRef r (mtail m))]
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
   e.g. pushStackFrame.
   However, most sane program blocks will preserve it. So far,
   preserving stack ids is a definition of sanity
   *)

val liveRefSTailSids : #a:Type -> r:(lref a) -> id:sidt  -> m0:memStack -> m1:memStack
  -> Lemma
   (requires (ssids m0 = ssids m1
            /\ refExistsInStack r id (stail m0)
            (*/\ refExistsInStack r id m0*)
            /\ refExistsInStack r id m1))
   (ensures refExistsInStack r id (stail m1))
let liveRefSTailSids r id m0 m1 =
(refExistsInStackId r id (stail m0))


val liveRefTailSids : #a:Type -> r:(lref a) -> m0:smem -> m1:smem -> Lemma
  (requires (sids m0 = sids m1 /\ liveRef r (mtail m0) /\ liveRef r m1))
  (ensures liveRef r (mtail m1))
  [SMTPat (sids m0 = sids m1)]
let liveRefTailSids r m0 m1 =
match (refLoc r) with
| InHeap -> ()
| InStack id -> (liveRefSTailSids r id (st m0) (st m1))



(** modifiesOnly and lemmas about it*)

(** cannot just uses ST.modifies. That was on heap; has to be lifted to smem.
Also, why does it's definition have to be so procedural, unlike the more declarative one below?
*)
type canModify  (m0 : smem)  (m1: smem) (rs: modset ) =
  forall (a:Type) (r: lref a).
      liveRef r m0
      ==> (~(Set.mem (Ref r) (reveal rs)))
      ==> (liveRef r m1 /\ (loopkupRef r m0 = loopkupRef r m1))


type  mreads (#a:Type) (r: lref a) (v:a) (m:smem) = liveRef r m /\ loopkupRef r m = v

(*lemmas needed for automatic inference*)
val canModifyNone : m:smem -> Lemma (canModify m m (hide empty))
let canModifyNone m = ()

val canModifyWrite : #a:Type -> r:(lref a) -> v:a -> m:smem
  -> Lemma (canModify m (writeMemAux r m v) (only  r))
let canModifyWrite r v m = ()

type mStackNonEmpty (m:smem) = b2t (isNonEmpty (st m))

(*val canModifySalloc : #a:Type -> r:(lref a) -> v:a -> m:smem
  -> Lemma (canModify m (writeMemAux r m v) (singleton (Ref r)))
let canModifyWrite r v m = ()*)


type allocateInBlock (#a:Type) (r: lref a) (h0 : region) (h1 : region) (init : a)   = not(contains h0 r) /\ contains h1 r /\  h1 == upd h0 r init

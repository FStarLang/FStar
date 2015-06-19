(*--build-config
    options:--admit_fsi Set;
    variables:LIB=../../lib;
    variables:MATHS=../maths;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst  $LIB/list.fst stack.fst listset.fst
  --*)



module StructuredMem
open Heap
open Stack
open Set
open Prims
open List
open ListSet

type sidt = nat



type memblock = heap
(*Can we ever define a memRep for a ref type?*)

(*How does List.memT work? is equality always decidable?*)

(* The axiomatization is agnostic
about resuse of memory ids, i.e. it should (provably) have both kind of models.
A client code's correctness/well-typedness cannot depend on stack-ids being reused.
This is actually a strictly weaker assumption, than the older one
where the client can potentially depend on stack ids being never reused.

This is similar to the case of freshness of references in ST.
The axiomatization is agnostic about whether a reference can be reused after it
is freed.
*)
type memStackAux = Stack (sidt * memblock)

val ssids : memStackAux ->  Tot (list sidt)
let ssids ms = mapT fst ms

val wellFormed : memStackAux -> Tot bool
let wellFormed ms = noRepeats (ssids ms)

type memStack = x:memStackAux{wellFormed x}


(* Should we also include sizes of refs in order to enable reasoninag about memory usage of programs?*)
(* What is the size of functions? Does it make even make sense to store a function at a reference? Would it be possible to transpile such a construct? *)

(* Free only makes sense for heaps. We can already reason about (absense of) memory leaks because one can talk about the domain of the heap*)
type smem = memblock * memStack


let hp (s : smem) = fst s

val st : smem -> Tot (Stack (sidt * memblock))
let st (s : smem) = (snd s)

val mtail : smem -> Tot smem
let mtail (s : smem) = (hp s, stail (st s))

val mstail : smem -> Tot ((Stack (sidt * memblock)))
let mstail (s : smem) = stail (st s)

val sids : smem -> Tot (list sidt)
let sids (m : smem) = ssids (st m)

let sid (s : (sidt * memblock)) = fst s

val topst : (s:smem{isNonEmpty (st s)}) -> Tot  (sidt * memblock)
let topst ss = (top (st ss))

val topstb : (s:smem{isNonEmpty (st s)}) ->  Tot memblock
let topstb ss = snd (topst ss)


val topstid : (s:smem{isNonEmpty (st s)}) ->  Tot sidt
let topstid ss = fst (topst ss)


type refLocType =
  | InHeap : refLocType
  | InStack : id:sidt -> refLocType

assume val refLoc : #a:Type -> ref a -> Tot refLocType

new_effect StSTATE = STATE_h smem

val stackBlockAtLoc : sidt  -> (Stack (sidt * memblock)) -> Tot (option memblock)
let rec stackBlockAtLoc id sp =
  match sp with
  | Nil -> None
  | h::tl -> if (id=(fst h)) then Some (snd h) else stackBlockAtLoc id tl


val blockAtLoc : smem -> refLocType  -> Tot (option memblock)
let blockAtLoc m rl =
match rl with
| InHeap -> Some (hp m)
| InStack id -> stackBlockAtLoc id (st m)

val writeInBlock : #a:Type -> r:(ref a) -> v:a -> memblock -> Tot memblock
let writeInBlock r v mb= upd mb r v

(* are there associative maps in FStar? *)
(*  proof by computation *)

val changeStackBlockWithId  : (memblock -> Tot memblock)
  -> sidt
  -> (Stack (sidt * memblock))
        -> Tot (Stack (sidt * memblock))
let rec changeStackBlockWithId f s ms=
match ms with
| [] -> []
| h::tl ->
  (if (fst h = s) then ((fst h, (f (snd h)))::tl) else h::(changeStackBlockWithId f s tl))

val writeInMemStack : #a:Type -> (ref a) -> (Stack (sidt * memblock)) -> sidt -> a -> Tot (Stack (sidt * memblock))
let rec writeInMemStack r ms s v = changeStackBlockWithId (writeInBlock r v) s ms

(*val freeInMemStack : #a:Type -> (ref a) -> (Stack (sidt * memblock)) -> sidt -> Tot (Stack (sidt * memblock))
let rec freeInMemStack r ms s = changeStackBlockWithId (freeRefInBlock r) s ms*)


val changeStackBlockSameIDs :
    f:(memblock -> Tot memblock) -> s:sidt -> ms:(Stack (sidt * memblock))
  -> Lemma (ensures ((ssids ms) = (ssids (changeStackBlockWithId f s ms))))
let rec changeStackBlockSameIDs f s ms =
match ms with
| Nil -> ()
| h::tl ->   if (fst h = s) then () else (changeStackBlockSameIDs f s tl)

val changeStackBlockWellFormed :
 f:(memblock -> Tot memblock) -> s:sidt -> ms:(Stack (sidt * memblock))
  -> Lemma
      (requires (wellFormed ms))
      (ensures (wellFormed (changeStackBlockWithId f s ms)))
let changeStackBlockWellFormed  f s ms = (changeStackBlockSameIDs f s ms)

val writeMemStackSameIDs : #a:Type -> r:(ref a) -> ms:(Stack (sidt * memblock))
  -> s:sidt -> v:a
  -> Lemma (ensures ((ssids ms) = (ssids (writeInMemStack r ms s v))))
let writeMemStackSameIDs r ms s v = (changeStackBlockSameIDs (writeInBlock r v) s ms)

val writeMemStackWellFormed : #a:Type -> r:(ref a)
  -> ms:(Stack (sidt * memblock))
  -> s:sidt -> v:a
  -> Lemma
      (requires (wellFormed (ms)))
      (ensures (wellFormed (writeInMemStack r ms s v)))
      [SMTPat (writeInMemStack r ms s v)]
let writeMemStackWellFormed r ms s v = (changeStackBlockWellFormed (writeInBlock r v) s ms)

(*val freeInMemStackSameIDs : #a:Type -> r:(ref a) -> ms:(Stack (sidt * memblock))
  -> s:sidt
  -> Lemma (ensures ((ssids ms) = (ssids (freeInMemStack r ms s))))
let freeInMemStackSameIDs r ms s = (changeStackBlockSameIDs (freeRefInBlock r) s ms)

val freeInMemStackWellFormed : #a:Type -> r:(ref a)
  -> ms:(Stack (sidt * memblock))
  -> s:sidt
  -> Lemma
      (requires (wellFormed (ms)))
      (ensures (wellFormed (freeInMemStack r ms s)))
      [SMTPat (freeInMemStack r ms s)]
let freeInMemStackWellFormed r ms s = (changeStackBlockWellFormed (freeRefInBlock r) s ms)*)

(* what is the analog of transport / eq_ind?*)

(*
val writeMemStackSameStail : #a:Type -> r:(ref a) -> ms:(Stack (sidt * memblock))
  -> s:sidt -> v:a
  -> Lemma (ensures ((stail ms) = (stail (writeInMemStack r ms s v))))
         (*  [SMTPat (writeMemStack r ms s v)] *)
let rec writeMemStackSameStail r ms s v = ()
*)


val refExistsInStack : #a:Type -> (ref a)
  -> id:sidt -> (Stack (sidt * memblock)) -> Tot bool
let rec refExistsInStack r id ms =
match ms with
| [] -> false
| h::tl -> if (fst h=id) then (Heap.contains (snd h) r) else refExistsInStack r id tl


val refExistsInStackId : #a:Type -> r:(ref a)
  -> id:sidt -> ms:(Stack (sidt * memblock))
  -> Lemma (requires (refExistsInStack r id ms))
          (ensures (memT id (ssids ms)))
let rec refExistsInStackId r id ms =
match ms with
| [] -> ()
| h::tl -> if (fst h=id) then () else (refExistsInStackId r id tl)

val memIdUniq:  h:(sidt * memblock) -> tl:memStackAux
  -> Lemma (requires (wellFormed (h::tl)))
        (ensures (notIn (fst h) (ssids tl)))
let memIdUniq h tl = ()


val refExistsInStackTail : #a:Type -> r:(ref a)
  -> id:sidt -> ms:memStack
  -> Lemma (requires (refExistsInStack r id (stail ms)))
          (ensures  (refExistsInStack r id ms))
          [SMTPat (refExistsInStack r id (stail ms))]
let refExistsInStackTail r id ms = (refExistsInStackId r id (stail ms))

(*match  (stackBlockAtLoc id ms)  with
                | Some b -> Heap.contains b r
                | None -> false*)

val refExistsInMem : #a:Type -> (ref a) -> smem ->  Tot bool
let refExistsInMem (#a:Type) (r:ref a) (m:smem) =
match (refLoc r) with
| InHeap -> Heap.contains (hp m) r
| InStack id -> refExistsInStack r id (st m)


val writeMemStackExists : #a:Type -> #b:Type -> rw:(ref a) -> r: (ref b)
  -> ms:(Stack (sidt * memblock))
  -> id:sidt -> idw:sidt -> v:a
  -> Lemma
      (requires (refExistsInStack r id ms))
      (ensures (refExistsInStack r id (writeInMemStack rw ms idw v)))
      [SMTPat (writeInMemStack rw ms id v)]
let rec writeMemStackExists rw r ms id idw v =
match ms with
| Nil -> ()
| h::tl ->   if (fst h = id) then () else ((writeMemStackExists rw r tl id idw v))

(* ((writeMemStackLem r ms s v)) *)

val writeMemAux : #a:Type -> (ref a) -> m:smem -> a -> Tot smem
let writeMemAux r m v =
  match (refLoc r) with
  | InHeap -> ((upd (hp m) r v), snd m)
  | InStack id -> ( (hp m), (writeInMemStack r (st m) id v) )


(*val freeMemAux : #a:Type -> (ref a) -> m:smem  -> Tot smem
let freeMemAux r m =
  match (refLoc r) with
  | InHeap -> ((freeRefInBlock r (hp m)), snd m)
  | InStack s -> ((hp m), ((freeInMemStack r (st m) s)))*)


val writeMemAuxPreservesExists :  #a:Type -> #b:Type ->
  rw:ref a -> r:ref b -> m:smem -> v:a ->
Lemma (requires (refExistsInMem r m))
      (ensures (refExistsInMem r (writeMemAux rw m v)))
      [SMTPat (writeMemAux rw m v)]
let writeMemAuxPreservesExists rw r m v =
match (refLoc r) with
| InHeap -> ()
| InStack id ->
    match (refLoc rw) with
    | InHeap -> ()
    | InStack idw ->  (writeMemStackExists rw r (st m) id idw v)


val writeMemAuxPreservesSids :  #a:Type -> rw:ref a  -> m:smem -> v:a ->
Lemma (requires (True)) (ensures (sids m = sids (writeMemAux rw m v)))
 [SMTPat (writeMemAux rw m v)]

let writeMemAuxPreservesSids rw m v =
match (refLoc rw) with
| InHeap -> ()
| InStack id ->  (writeMemStackSameIDs rw (st m) id v)


(*
val writeMemAuxPreservesStail :  #a:Type -> r:(ref a) -> m:smem -> v:a ->
Lemma (requires (is_InStack (refLoc r)))
  (ensures mtail m = mtail (writeMemAux r m v))
let rec writeMemAuxPreservesStail r m v =  ()
*)

val loopkupRefStack : #a:Type -> r:(ref a) -> id:sidt -> ms:(Stack (sidt * memblock)){refExistsInStack r id ms}  ->  Tot a
let rec loopkupRefStack r id ms =
match ms with
| h::tl ->
    if (fst h = id) then  sel (snd h) r else (loopkupRefStack r id tl)


(* it is surprising that sel always returns something; It might be tricky to implement it.
   What prevents me from creating a ref of an empty type? Perhaps it is impossible to create a member
   of the type (ref False) . For example, the memory allocation operator, which creates a new (ref 'a)
   requires an initial value of type 'a
*)
val loopkupRef : #a:Type -> r:(ref a) -> m:smem{(refExistsInMem r m) == true} ->  Tot a
let loopkupRef r m =
match (refLoc r) with
| InHeap -> (sel (hp m) r)
| InStack id -> loopkupRefStack r id (st m)


val readAfterWriteStack :
  #a:Type -> rw:(ref a) -> r:(ref a) -> v:a -> id:sidt -> idw:sidt -> m:(Stack (sidt * memblock)) ->
  Lemma (requires (refExistsInStack r id m))
        (ensures true)
        (*  (ensures ((refExistsInStack r id m)
            /\ loopkupRefStack r id (writeInMemStack rw m idw v) = (if (r=rw) then v else (loopkupRefStack r id m)))) *)

type ifthenelseT (b:Type) (tc : Type) (fc: Type) =
 (b ==>  tc) /\ ((~b) ==> fc )

val readAfterWriteStack :
  #a:Type  -> #b:Type -> rw:(ref a) -> r:(ref b) -> v:a -> id:sidt -> idw:sidt -> m:(Stack (sidt * memblock)) ->
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
  #a:Type -> rw:(ref a) -> r:(ref a) -> v:a -> id:sidt -> idw:sidt -> m:(Stack (sidt * memblock)) ->
  Lemma (requires (refExistsInStack r id m))
        (ensures ((refExistsInStack r id m)
            /\ loopkupRefStack r id (writeInMemStack rw m idw v) = (if (r=rw && id=idw) then v else (loopkupRefStack r id m))))
let readAfterWriteStackSameType rw r v id idw m = readAfterWriteStack rw r v id idw m

val readAfterWrite : #a:Type -> #b:Type ->  rw:(ref a) -> r:(ref b) -> v:a -> m:smem ->
  Lemma (requires (refExistsInMem r m))
        (ensures (refExistsInMem r m)
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
val readAfterWriteTrue : #a:Type -> #b:Type ->  rw:(ref a) -> r:(ref b) -> v:a -> m:smem ->
  Lemma (requires (refExistsInMem r m /\ r==rw))
        (ensures (refExistsInMem r m) /\
            (loopkupRef r (writeMemAux rw m v) == v))
        [SMTPat (writeMemAux rw m v)]
let readAfterWriteTrue rw r v m = readAfterWrite rw r v m


val readAfterWriteFalse : #a:Type -> #b:Type ->  rw:(ref a) -> r:(ref b) -> v:a -> m:smem ->
  Lemma (requires (refExistsInMem r m /\ r=!=rw))
        (ensures (refExistsInMem r m) /\
        (loopkupRef r (writeMemAux rw m v) = (loopkupRef r m)))
        [SMTPat (writeMemAux rw m v)]
let readAfterWriteFalse rw r v m = readAfterWrite rw r v m


(*perhaps this specialization is not requires anymore*)
val readAfterWriteSameType : #a:Type -> rw:(ref a) -> r:(ref a) -> v:a -> m:smem ->
  Lemma (requires (refExistsInMem r m))
        (ensures (refExistsInMem r m)
            /\ loopkupRef r (writeMemAux rw m v) = (if (r=rw) then v else (loopkupRef r m)))
let readAfterWriteSameType rw r v m = readAfterWrite rw r v m


val refExistsInMemTail : #a:Type -> r:(ref a) -> m:smem ->
  Lemma (requires (refExistsInMem r (mtail m)))
        (ensures (refExistsInMem r (m)))
        [SMTPat (refExistsInMem r (mtail m))]
let refExistsInMemTail r m =
match (refLoc r) with
| InHeap -> ()
| InStack id -> (refExistsInStackTail r id (st m))

val loopkupRefStackTail
  : #a:Type -> r:(ref a) -> id:sidt -> m:memStack
    ->  Lemma
   (requires (refExistsInStack r id (stail m)))
    (ensures ((refExistsInStack r id (stail m)) /\ loopkupRefStack r id m
        = loopkupRefStack r id (stail m)))
let loopkupRefStackTail r id ms = (refExistsInStackId r id (stail ms))


val readTailRef : #a:Type -> r:(ref a) -> m:smem ->
  Lemma (requires (refExistsInMem r (mtail m)))
        (ensures (refExistsInMem r (mtail m))
            /\ loopkupRef r m =  loopkupRef r (mtail m))
            [SMTPat (refExistsInMem r (mtail m))]
let readTailRef r m =
match (refLoc r) with
| InHeap -> ()
| InStack id -> (loopkupRefStackTail r id (st m))


val writeStackTail
  : #a:Type -> r:(ref a) -> id:sidt -> v:a -> m:memStack
    ->  Lemma
      (requires (refExistsInStack r id (stail m)))
      (ensures (stail (writeInMemStack r m id v)
                    = writeInMemStack r (stail m) id v))
let writeStackTail r id v ms = (refExistsInStackId r id (stail ms))

val writeTailRef : #a:Type -> r:(ref a) -> m:smem -> v:a ->
  Lemma (requires (refExistsInMem r (mtail m)))
        (ensures (refExistsInMem r (mtail m))
            /\ mtail (writeMemAux r m v) =  writeMemAux r (mtail m) v)
            [SMTPat (refExistsInMem r (mtail m))]
let writeTailRef r m v =
match (refLoc r) with
| InHeap -> ()
| InStack id -> (writeStackTail r id v (st m))

(* The location of a ref (say r) is refLoc r, and is independent of the
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

val refExistsInMemSTailSids : #a:Type -> r:(ref a) -> id:sidt  -> m0:memStack -> m1:memStack
  -> Lemma
   (requires (ssids m0 = ssids m1
            /\ refExistsInStack r id (stail m0)
            (*/\ refExistsInStack r id m0*)
            /\ refExistsInStack r id m1))
   (ensures refExistsInStack r id (stail m1))
let rec refExistsInMemSTailSids r id m0 m1 =
(refExistsInStackId r id (stail m0))


val refExistsInMemTailSids : #a:Type -> r:(ref a) -> m0:smem -> m1:smem -> Lemma
  (requires (sids m0 = sids m1 /\ refExistsInMem r (mtail m0) /\ refExistsInMem r m1))
  (ensures refExistsInMem r (mtail m1))
  (*[SMTPat (sids m0 = sids m1)]*)
let refExistsInMemTailSids r m0 m1 =
match (refLoc r) with
| InHeap -> ()
| InStack id -> (refExistsInMemSTailSids r id (st m0) (st m1))



(** modifiesOnly and lemmas about it*)

(** cannot just uses ST.modifies. That was on heap; has to be lifted to smem.
Also, why does it's definition have to be so procedural, unlike the more declarative one below?
*)

type canModify  (m0 : smem)  (m1: smem) (rs: set aref ) =
  forall (a:Type) (r: ref a).
      refExistsInMem r m0
      ==> (~(Set.mem (Ref r) rs))
      ==> (refExistsInMem r m1 /\ (loopkupRef r m0 = loopkupRef r m1))


type  mreads (#a:Type) (r: ref a) (v:a) (m:smem) = refExistsInMem r m /\ loopkupRef r m = v

(*lemmas needed for automatic inference*)
val canModifyNone : m:smem -> Lemma (canModify m m empty)
let canModifyNone m = ()

val canModifyWrite : #a:Type -> r:(ref a) -> v:a -> m:smem
  -> Lemma (canModify m (writeMemAux r m v) (singleton (Ref r)))
let canModifyWrite r v m = ()


(*val canModifySalloc : #a:Type -> r:(ref a) -> v:a -> m:smem
  -> Lemma (canModify m (writeMemAux r m v) (singleton (Ref r)))
let canModifyWrite r v m = ()*)


(*perhaps we also need canModify version of the while combinator.
Currently it is annoying to carry around non-modification properties in
loop invariants. One has to carry around an extra parameter denoting the value
at the beginning of the loop. canModify an perhaps alleviate this problem
*)

(*should extend to types with decidable equality*)
(*val is1SuffixOf : list sidt -> list sidt -> Tot bool
let is1SuffixOf lsmall lbig =
match lbig with
| [] -> false
| h::tl -> tl=lsmall*)

type allocateInBlock (#a:Type) (r: ref a) (h0 : memblock) (h1 : memblock) (init : a)   = not(Heap.contains h0 r) /\ Heap.contains h1 r /\  h1 == upd h0 r init

kind Pre  = smem -> Type
kind Post (a:Type) = a -> smem -> Type

effect SST (a:Type) (pre:Pre) (post: (smem -> Post a)) =
        StSTATE a
              (fun (p:Post a) (h:smem) -> pre h /\ (forall a h1. (pre h  /\ post h a h1) ==> p a h1)) (* WP *)
              (fun (p:Post a) (h:smem) -> (forall a h1. (pre h  /\ post h a h1) ==> p a h1))          (* WLP *)

assume val halloc:  #a:Type -> init:a -> SST (ref a)
                                         (fun m -> True)
                                         (fun m0 r m1 -> allocateInBlock r (hp m0)  (hp m1) init /\ (snd m0 = snd m1) /\ refLoc r == InHeap)

assume val salloc:  #a:Type -> init:a -> SST (ref a)
     (fun m -> b2t (isNonEmpty (st m))) (*why is "== true" required here, but not at other places? : *)
     (*Does F* have (user defined?) implicit coercions? : Not yet *)
     (fun m0 r m1 ->
          (isNonEmpty (st m0)) /\ (isNonEmpty (st m1))
          /\ allocateInBlock r (topstb m0) (topstb m1) init
          /\ refLoc r = InStack (topstid m0) /\ (topstid m0 = topstid m1)
          /\ mtail m0 = mtail m1)

assume val memread:  #a:Type -> r:(ref a) -> SST a
	  (fun m -> b2t (refExistsInMem r m))
    (fun m0 a m1 -> m0=m1 /\ (refExistsInMem r m0) /\ loopkupRef r m0 = a)

assume val memwrite:  #a:Type -> r:(ref a) -> v:a ->
  SST unit
	    (fun m -> b2t (refExistsInMem r m))
      (fun m0 _ m1 -> (refExistsInMem r m1)
        /\ (writeMemAux r m0 v) =  m1)

(*
Free can only deallocate a heap-allocated ref. The implementation
below doesn't make sense becasue it allows even deallocation of stack
references

assume val freeRef:  #a:Type -> r:(ref a)  ->
  SST unit
	    (fun m -> b2t (refExistsInMem r m))
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

(*
sub_effect
  PURE  ~> StSTATE = fun (a:Type) (wp:PureWP a) (p : SSTPost a) (h:smem)
            -> wp (fun a -> p a h)
*)

(* should we have an SSTP  for pure SST which has a lifting from PURE,
   and a lifting from SSTP and DIV to SST?
    It seems like a bad idea to have a blank check for non-termination.
    One can carefully restrict and explicitly identify the programs that
    really need non-termination *)

type mStackNonEmpty (m:smem) = b2t (isNonEmpty (st m))




(*Sane SST*)
effect Mem (a:Type) (pre:Pre) (post: (smem -> Post a)) (mod:set aref) =
        SST a pre (fun m0 a m1 -> post m0 a m1 /\ sids m0 = sids m1 /\ canModify m0 m1 mod)

effect PureMem (a:Type) (pre:Pre) (post: (smem -> Post a)) =
        SST a pre (fun m0 a m1 -> post m0 a m1 /\ m0=m1)

(*incase one does not want to reason about changed references*)
let allRefs : set aref = complement empty

(** withNewStackFrame combinator *)
(*adding requires/ensures here causes the definition of scopedWhile below to not typecheck.
Hope this is not a concert w.r.t. soundness*)
effect WNSC (a:Type) (pre:(smem -> Type))  (post: (smem -> SSTPost a)) (mod:set aref) =
  Mem a
      ( (*requires *) (fun m -> isNonEmpty (st m) /\ topstb m = emp /\ pre (mtail m)))
      ( (* ensures *) (fun m0 a m1 -> post (mtail m0) a (mtail m1)))
      mod

val withNewScope : #a:Type -> #pre:(smem -> Type) -> #post:(smem -> SSTPost a)
  -> #mod:set aref
  -> body:(unit -> WNSC a pre post mod)
      -> Mem a pre post mod
let withNewScope 'a 'pre 'post #mod body =
    pushStackFrame ();
    let v = body () in
    popStackFrame (); v

(*SMTPat could be used to implement something similar to Coq's type-class mechanism.
Coq's typeclass resolution is based on proof search using Hint databases, which is similar to SMTPat.
Can implicit arguments be inferred automatically by the SMT solver using proof seach with SMTPat hints?
*)


(*a combinator for writing while loops*)

(*Mem restriction is not needed, because there is a even stronger condition here that the memory is unchanges*)
effect whileGuard (pre :(smem -> Type))
  (lc : (smem -> Type))
  = PureMem bool  pre (fun m0 b _ ->   (lc m0 <==> b = true))
(* the guard of a while loop is not supposed to change the memory*)

effect whileBody (loopInv:smem -> Type) (lc:smem  -> Type) (mod:set aref)
  = WNSC unit (fun m -> loopInv m /\ lc m)
              (fun _ _ m1 -> loopInv m1)
              mod



val scopedWhile : loopInv:(smem -> Type)
  -> wglc:(smem -> Type)
  -> wg:(unit -> whileGuard loopInv wglc)
  -> mod:(set aref)
  -> bd:(unit -> whileBody loopInv wglc mod)
  -> Mem unit (requires (fun m -> loopInv m))
              (ensures (fun m0 _ m1 -> loopInv m1 /\ (~(wglc m1))))
              mod
let rec scopedWhile
   'loopInv 'wglc wg mod bd =
   if (wg ())
      then
        ((withNewScope #unit
            #(fun m -> 'loopInv m /\ ('wglc m)) #(fun _ _ m1 -> 'loopInv m1) #mod bd);
        (scopedWhile 'loopInv 'wglc wg mod bd))
      else ()


val scopedWhile1 :
  #a:Type
  -> r:(ref a)
  -> lc : (a -> Tot bool)
  -> loopInv:(smem -> Type)
  -> mod:(set aref)
  -> bd:(unit -> WNSC unit (fun m -> loopInv m /\ refExistsInMem r m /\ (lc (loopkupRef r m)))
              (fun _ _ m1 -> loopInv m1 /\ refExistsInMem r m1) mod )
  -> Mem unit ((fun m -> loopInv m /\ refExistsInMem r m))
              ((fun m0 _ m1 -> loopInv m1 /\ refExistsInMem r m1 /\ ~(lc (loopkupRef r m1))))
              mod
let scopedWhile1 'a r lc 'loopInv mod bd =
  scopedWhile
  (*augment the loop invariant to include the precondition for evaluating the guard*)
    (fun m -> 'loopInv m /\ refExistsInMem r m)
    (fun m -> refExistsInMem r m /\ (lc (loopkupRef r m)))
    (fun u -> lc (memread r))
    mod
    bd

val scopedWhile2 :
  #a:Type
  -> #b:Type
  -> ra:(ref a)
  -> rb:(ref b)
  -> lc : (a -> b ->  Tot bool)
  -> loopInv:(smem -> Type)
  -> mod:(set aref)
  -> bd:(unit -> WNSC unit (fun m -> loopInv m /\ refExistsInMem ra m /\ refExistsInMem rb m /\ (lc (loopkupRef ra m) (loopkupRef rb m)))
              (fun _ _ m1 -> loopInv m1 /\ refExistsInMem ra m1 /\ refExistsInMem rb m1) mod)
  -> Mem unit (requires (fun m -> loopInv m /\ refExistsInMem ra m /\ refExistsInMem rb m))
              (ensures (fun m0 _ m1 -> loopInv m1 /\ refExistsInMem ra m1 /\ refExistsInMem rb m1 /\ ~(lc (loopkupRef ra m1) (loopkupRef rb m1)) ))
              mod
let scopedWhile2 'a ra rb lc 'loopInv mod bd =
  scopedWhile
  (*augment the loop invariant to include the precondition for evaluating the guard*)
    (fun m -> 'loopInv m /\ refExistsInMem ra m /\ refExistsInMem rb m)
    (fun m -> refExistsInMem ra m /\ refExistsInMem rb m /\ (lc (loopkupRef ra m) (loopkupRef rb m))  )
    (fun u -> lc (memread ra) (memread rb))
    mod
    bd

(*effect SSTS (a:Type) (wlp: Post a -> Pre) = StSTATE a wlp wlp*)

(*type whilePre (wpg:(Post bool -> Pre))
              (wpb:(Post unit -> Pre))
              (inv:(smem -> Type)) =
  (forall h. forall h2. wpg (fun b h1 -> h1 == h) h2 ==> h=h2) (*computation of the guard does not change the memory*)
  /\ (forall h1. inv h1 ==> wpg (fun b h2 -> b=true ==> wpb (fun _ -> inv) h2) h1)

val scopedWhile2 : #wpg:(Post bool -> Pre) -> #wpb:(Post unit -> Pre)
  -> wg:(unit -> SSTS bool wpg)
  -> bd:(unit -> SSTS unit wpb)
  -> loopInv:(smem -> Type)
  -> SST unit
  (requires (fun m -> loopInv m /\ whilePre wpg wpb loopInv))
              (ensures (fun m0 _ m1 -> (loopInv m1) (* /\ sids m0 = sids m1 *)
                (*/\ (wpg (fun b _ -> b==false) m1)*)
              ))*)

(*let scopedWhile2
 (#wpg:(Post bool -> Pre))
 (#wpb:(Post unit -> Pre))
 (wg:(unit -> SSTS bool wpg))
 (bd:(unit -> SSTS unit wpb))
 (loopInv:(smem -> Type))
= let v=wg () in ()*)

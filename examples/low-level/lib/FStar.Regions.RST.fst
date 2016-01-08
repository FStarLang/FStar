(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Ghost.fst FStar.List.Tot.fst FStar.Stack.fst FStar.Regions.Located.fst FStar.Regions.Heap.fst FStar.Regions.Regions.fst
  --*)

module FStar.Regions.RST

(** This module defines the [FStar.Regions.RST] effect of computations that occur within our
    stack of regions. *)

open FStar.Regions.Located
open FStar.Regions.Heap
open FStar.Regions.Regions


kind Pre  = smem -> Type
(* JP: This is the same thing as [STPost_h smem a]. *)
kind Post (a:Type) = a -> smem -> Type

new_effect RSTATE = STATE_h smem

effect RST (a:Type) (pre:Pre) (post: (smem -> Post a)) =
  RSTATE a
    (fun (p:Post a) (h:smem) -> pre h /\ (forall a h1. (pre h /\ post h a h1) ==> p a h1)) (* WP *)
    (fun (p:Post a) (h:smem) -> (forall a h1. (pre h /\ post h a h1) ==> p a h1)) (* WLP *)

//JP, NS: Can we implement RST on top of ST somehow? 
//That would allow us to reuse the soundness argument of ST for the region calculus we build on top of it. 
//Perhaps one strategy is to rely on a single ref cell provided by the ST monad to implement the entire region hierarchy
//within it. The tricky bit is to figure out how to hide this implementation detail from clients of RST.
//Also, we need to do something to model new name generation.

(** Operations for allocation, reading and writing into our new (axiomatized)
    memory. The functions below are axiomatized, because when extracting to
    OCaml code, we replace them with calls to our custom memory allocator. *)

(* Allocate an [lref] in the garbage-collected heap. This is the [ref] ML function. *)
assume val halloc: #a:Type -> init:a ->
  RST (lref a)
    (fun m -> True)
    (fun m0 r m1 -> allocatedInRegion r (hp m0) (hp m1) init /\ snd m0 = snd m1 /\ regionOf r = InHeap)

(* Allocate an [lref] in the top-most region. This is a new, [ref]-like function. *)
assume val ralloc:  #a:Type -> init:a -> RST (lref a)
     mStackNonEmpty
     (fun m0 r m1 ->
          mStackNonEmpty m0 /\ mStackNonEmpty m1
          /\ allocatedInRegion r (topRegion m0) (topRegion m1) init
          /\ regionOf r = InStack (topRegionId m0) /\ topRegionId m0 = topRegionId m1
          /\ Regions.tail m0 = Regions.tail m1 /\ m1 = allocateInTopR r init m0)


(* Read from the top-most region. This is the [!] ML operator. *)
assume val memread:  #a:Type -> r:lref a ->
  RST a
    (fun m -> b2t (refIsLive r m))
    (fun m0 a m1 -> m0=m1 /\ refIsLive r m0 /\ lookupRef r m0 = a)

(* Write in the top-most region. This is the [:=] ML operator. *)
assume val memwrite:  #a:Type -> r:lref a -> v:a ->
  RST unit
    (fun m -> b2t (refIsLive r m))
    (fun m0 _ m1 -> refIsLive r m1
               /\ writeMemAux r m0 v =  m1)


(** Two operations for manipulating the stack of regions. *)
assume val pushRegion:  unit -> RST unit
    (fun m -> True)
    (fun m0 _ m1 ->
             Regions.tail m1 = m0
          /\ Stack.isNonEmpty (st m1)
          /\ topRegion m1 = emp)

assume val popRegion:  unit -> RST unit
    mStackNonEmpty
    (fun m0 _ m1 -> Regions.tail m0 == m1)


(** Injection of the [DIV] effect into the [RST] effect, mostly copied from prims.fst *)
sub_effect
  DIV  ~> RSTATE = fun (a:Type) (wp:PureWP a) (p: Post a) (h:smem)
                -> wp (fun a -> p a h)


(** Some effect abbreviations. *)

(* Effect of a computation that leaves the region stack's structure unchanged
   (i.e. no push or pop) but may read or modify any live reference in [mod]. *)
effect Mem (a:Type) (pre: smem -> Type) (post: (smem -> Post a)) (mod: FStar.Regions.Heap.modset) =
        RST a pre (fun m0 a m1 -> post m0 a m1 /\ rids m0 = rids m1 /\ canModify m0 m1 mod)

(* Effect of a computation that leaves the region stack's structure unchanged
   (i.e. no push or pop), but may read any live reference. *)
effect PureMem (a:Type) (pre:smem -> Type) (post: smem -> a -> Type) =
        RST a pre (fun m0 a m1 -> post m1 a /\ m0 = m1)

(* Equivalent of the [Heap.get] function that allows one to talk about the
   [smem] in specifications. *)
assume val get : unit -> PureMem (Ghost.erased smem)
      (requires (fun m -> true))
      (ensures (fun m v -> Ghost.reveal v = m))


(** [lalloc] is the final combinator -- notice that it is in the effect
    [PureMem], meaning that it does not change the map from references to their
    values. Indeed, its purpose is to allocate _immutable_ values in our stack
    of regions. For that to happen, the type [a] must satisfy the predicates
    [locatable a] (TODO) and [immutable a] (TODO as well).

    Because this combinator does not rely on the ghost heap that's built into
    [RST] to keep track of the ghost value of [l], we provide an extra
    assumption in the post-condition.

    Another restriction on the use of [lalloc] is that its argument should be a
    head-normal form of the type. This is currently enforced at the extraction
    level since this is not something we can express in the type system.

    Note: if the location of this combinator changes,
    [src/extraction/ml-syntax.fs] must be updated. *)
assume val lalloc: #a:Type -> v:a -> PureMem
  (located a)
  (requires mStackNonEmpty)
  (ensures (fun m1 l -> lreveal l = v /\ Stack.isNonEmpty (st m1) /\ regionOf l = InStack (topRegionId m1)))


(* //TODO: This is not sound; take f as the identity function *)
(* //      The intended semantics is to restrict f to be a strict projector of 'a *)
(* assume val llift : f:('a -> Tot 'b) -> l:located 'a *)
(* -> PureMem 'b (requires (fun m-> locIsLive l m)) *)
(*               (ensures (fun v m1 -> v == f (lreveal l) )) *)

(*
e.g., components (code (a * b)) c = a -> b -> Tot c;
but this requires type-to-type functions functions

assume val llift : #a:Type -> #b:Type -> f:(components a b) -> l:located a
-> PureMem 'b (requires (fun m-> liveLoc l m))
              (ensures (fun v m1 -> v == f (greveal l) ))


*)

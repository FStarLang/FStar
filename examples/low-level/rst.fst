(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:ext.fst set.fsi heap.fst st.fst all.fst list.fst
      stack.fst listset.fst ghost.fst located.fst lref.fst regions.fst
  --*)

module RST

(** This module defines the [RST] effect of computations that occur within our
    stack of regions. *)

open Located
open Regions
open Lref

kind Pre  = smem -> Type
kind Post (a:Type) = a -> smem -> Type

new_effect StSTATE = STATE_h smem

effect RST (a:Type) (pre:Pre) (post: (smem -> Post a)) =
  StSTATE a
    (fun (p:Post a) (h:smem) -> pre h /\ (forall a h1. (pre h /\ post h a h1) ==> p a h1)) (* WP *)
    (fun (p:Post a) (h:smem) -> (forall a h1. (pre h /\ post h a h1) ==> p a h1)) (* WLP *)


(** Operations for allocation, reading and writing into our new (axiomatized)
    memory. The functions below are axiomatized, because when extracting to
    OCaml code, we replace them with calls to our custom memory allocator. *)

(* Allocate in the garbage-collected heap. This is the [ref] ML function. *)
assume val halloc: #a:Type -> init:a ->
  RST (lref a)
    (fun m -> True)
    (fun m0 r m1 -> allocatedInRegion r (hp m0) (hp m1) init /\ (snd m0 = snd m1) /\ refLoc r == InHeap)

(* Allocate in the top-most region. This is a new, [ref]-like function. *)
assume val ralloc:  #a:Type -> init:a -> RST (lref a)
     mStackNonEmpty
     (fun m0 r m1 ->
          Stack.isNonEmpty (st m0) /\ Stack.isNonEmpty (st m1)
          /\ allocatedInRegion r (topRegion m0) (topRegion m1) init
          /\ refLoc r = InStack (topRegionId m0) /\ topRegionId m0 = topRegionId m1
          /\ Regions.tail m0 = Regions.tail m1 /\ m1 = allocateInTopR r init m0)


(* Read from the top-most region. This is the [!] ML operator. *)
assume val memread:  #a:Type -> r:lref a ->
  RST a
    (fun m -> b2t (liveRef r m))
    (fun m0 a m1 -> m0=m1 /\ liveRef r m0 /\ lookupRef r m0 = a)

(* Write in the top-most region. This is the [:=] ML operator. *)
assume val memwrite:  #a:Type -> r:lref a -> v:a ->
  RST unit
    (fun m -> b2t (liveRef r m))
    (fun m0 _ m1 -> liveRef r m1
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
kind RSTPost (a:Type) = STPost_h smem a

sub_effect
  DIV  ~> StSTATE = fun (a:Type) (wp:PureWP a) (p : RSTPost a) (h:smem)
                -> wp (fun a -> p a h)

(** Some effect abbreviations. *)

(* Effect of a computation that leaves the region stack's structure unchanged
   (i.e. no push or pop) but may *)
effect Mem (a:Type) (pre: smem -> Type) (post: (smem -> RSTPost a)) (mod: modset) =
        RST a pre (fun m0 a m1 -> post m0 a m1 /\ rids m0 = rids m1 /\ canModify m0 m1 mod)

//TODO: MemReader?
effect PureMem (a:Type) (pre:smem -> Type) (post: smem -> a -> Type) =
        RST a pre (fun m0 a m1 -> post m1 a /\ m0=m1)

assume val get : unit -> PureMem (FStar.Ghost.erased smem)
      (requires (fun m -> true))
      (ensures (fun m v -> FStar.Ghost.reveal v = m))

(*
 * In future, we would like to enforce that the type a is locatable and immutable.
 * See a precise definition of locatable in located.fst.
 * When allocating mutable things, the ghost memory of RST must be updated to
 * keep track of its "current" value. Because lalloc is a PureMem, it cannot be used.
 * PureMem means lalloc does not change smem, the map from references to their values.
 * For refs, use instead ralloc above. for arrays, use [hs]create in array.fsi instead.
 *)
 (*is this is ever renamed or moved, mlp_lalloc in src\extraction\ml-syntax.fs MUST be updated.*)
 (*as of now, a can only be a record type.*)
(*for efficiency, the argument to lalloc should be a head normal form of the type.
Extraction will then avoid creating this value on the heap.*)
assume val lalloc: #a:Type -> v:a -> PureMem
  (located a)
  (requires mStackNonEmpty)
  (ensures (fun m1 l -> lreveal l = v /\ Stack.isNonEmpty (st m1) /\ regionOf l = InStack (topRegionId m1)))

//TODO: This is not sound; take f as the identity function
//      The intended semantics is to restrict f to be a strict projector of 'a
assume val llift : f:('a -> Tot 'b) -> l:located 'a
-> PureMem 'b (requires (fun m-> liveLoc l m))
              (ensures (fun v m1 -> v == f (lreveal l) ))

(*
e.g., components (code (a * b)) c = a -> b -> Tot c;
but this requires type-to-type functions functions

assume val llift : #a:Type -> #b:Type -> f:(components a b) -> l:located a
-> PureMem 'b (requires (fun m-> liveLoc l m))
              (ensures (fun v m1 -> v == f (greveal l) ))


*)


(*
Free can only deallocate a heap-allocated lref. The implementation
below doesn't make sense becasue it allows even deallocation of stack
references

assume val freeRef:  #a:Type -> r:(lref a)  ->
  RST unit
	    (fun m -> b2t (liveRef r m))
      (fun m0 _ m1 -> (freeMemAux r m0) ==  m1)
*)

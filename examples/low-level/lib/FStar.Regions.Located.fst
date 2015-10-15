(*--build-config
    other-files:ghost.fst
  --*)

module FStar.Regions.Located

open FStar.Ghost

(** [located t] is the same thing as [t]; the extra type constructor
    is there to make sure we go through the special combinators when
    dereferencing a [located t]. The type only makes sense for
    heap-allocated data, but we currently lack a builtin [locatable t]
    predicate. *)
type located : Type -> Type // AA: implement this as a private pair (a * regionLoc)

//JP,NS: The (a * regionLoc) model is very low fidelity. 
//It would allow us to also implement bogus functions like 
//val locate' : a -> Tot (located a{regionOf l = InStack 17})
//which, informally, is unsound. 
//Would be good to pick a model for located that allows us to realize 
//only the functions that we informally argue are sound.
//Maybe that would involve building located t on top of FStar.Regions.RST somehow.

(** Each region on the stack is tagged with a region id [rid]. *)
type rid = nat

(** Therefore, when locating an object, it's either in the heap or in
    our stack of regions. *)
type regionLoc =
| InHeap : regionLoc
| InStack : id:rid -> regionLoc

(** An abstract predicate that tags a [located t] with the region it
    lives in. We have the invariant that for each [x:located t] we
    have, there exists a corresponding [regionOf x] predicate in the
    environment. *)
assume val regionOf : #a:Type -> located a -> Tot regionLoc // JP: GTot here?

(** For specification purposes, we want to actually know that [located
    t] is, really, [t]. *)
assume val lhide : #a:Type -> l:located a -> Tot (erased a)

(** XXX this combinator is strange. Need to find a better name. *)
val lreveal : #a:Type -> l:located a  -> GTot a
let lreveal l = reveal (lhide l)

(** One can always locate an existing value (it's in the heap). *)
assume val locate: #a:Type -> v:a -> Tot (l:located a{regionOf l = InHeap /\ lreveal l = v})

(** Discarding the location information is sound only if the object
    was allocated in the heap. *)
assume val unlocate: #a:Type -> l:located a{regionOf l = InHeap} -> Tot (v:a{lreveal l = v})

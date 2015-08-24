(*--build-config
other-files: ../../lib/ghost.fst
  --*)


module Located
open Ghost

(*in future, one located will take as input only locatable types.
  A type T is located iff some members of type T are represented in OCaml as
  memory addresses. Examples are references, pairs, etc.
  regionOf below is supposed to return whether that address points to the OCaml
  heap or to Mike's C heap
*)
type located : Type -> Type //implement this as an private pair (a * regionLoc) TODO
type sidt = nat

type regionLoc =
  | InHeap : regionLoc
  | InStack : id:sidt -> regionLoc

assume val regionOf : #a:Type -> located a -> Tot regionLoc //the return type of this should be either erased TODO
assume val lreveal : #a:Type -> l:located a  -> Tot (erased a)

val greveal : #a:Type -> l:located a  -> GTot a
let greveal l = reveal (lreveal l)

(*for region(stack) allocated stuff, lalloc will have a spec w.r.t reveal*)
assume val locate: #a:Type -> v:a -> Tot (l:located a{regionOf l= InHeap /\  greveal l =v})
assume val unlocate: #a:Type -> l:located a{regionOf l = InHeap} -> Tot (v:a{greveal l =v})

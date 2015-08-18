(*--build-config
other-files: ../../lib/ghost.fst
  --*)


module Located
open Ghost

type located : Type -> Type

type sidt = nat

type regionLoc =
  | InHeap : regionLoc
  | InStack : id:sidt -> regionLoc

assume val regionOf : #a:Type -> located a -> Tot regionLoc

assume val lreveal : #a:Type -> l:(located a)  -> Tot (erased a)

val greveal : #a:Type -> l:(located a)  -> GTot a
let greveal l = reveal (lreveal l)

(*for region(stack) allocated stuff, lalloc will have a spec w.r.t reveal*)
assume val locate: #a:Type -> v:a -> Tot (l:(located a){regionOf l= InHeap /\  greveal l =v})

assume val unlocate: #a:Type -> l:(located a){regionOf l = InHeap}
  -> Tot (v:a{greveal l =v})

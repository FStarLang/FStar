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

assume val unlocate: #a:Type -> l:(located a){regionOf l = InHeap}  -> Tot a

assume val locate: #a:Type -> v:a -> Tot (l:(located a){regionOf l= InHeap /\ unlocate l =v})

assume val lreveal : #a:Type -> l:(located a)  -> Tot (v:(erased a){(regionOf l = InHeap) ==> (reveal v = unlocate l)})
(*for region(stack) allocated stuff, lalloc will have a spec w.r.t reveal*)

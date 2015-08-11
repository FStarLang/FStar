(*--build-config
  --*)


module Located


type located : Type -> Type

type sidt = nat

type regionLoc =
  | InHeap : regionLoc
  | InStack : id:sidt -> regionLoc

assume val regionOf : #a:Type -> located a -> Tot regionLoc

assume val locate: #a:Type -> a -> Tot (l:(located a){regionOf l= InHeap})

assume val unlocate: #a:Type -> l:(located a){regionOf l = InHeap}  -> Tot a

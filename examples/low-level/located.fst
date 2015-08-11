(*--build-config
    variables:LIB=../../lib;
    variables:MATHS=../maths;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/set.fst $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/list.fst stack.fst listset.fst $LIB/ghost.fst
  --*)

(*     options: --codegen OCaml-experimental --trace_error --debug yes --prn; *)

module Located


open Ghost
type located : Type -> Type

type sidt = nat

(* TODO : use these in stackAndHeap.fst *)
type regionLoc =
  | InHeap : regionLoc
  | InStack : id:sidt -> regionLoc

assume val regionOf : #a:Type -> located a -> Tot regionLoc

assume val locate: #a:Type -> a -> Tot (l:(located a){regionOf l= InHeap})

assume val unlocate: #a:Type -> l:(located a){regionOf l = InHeap}  -> Tot a

(*--build-config
    options:--admit_fsi FStar.Set --z3timeout 5 --project_module TEST --project_module TEST2 --project_module TEST3;
    variables:LIB=../../../lib;
    other-files:$LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/st2.fst 
  --*)

module Projection
open FStar.Heap
open FStar.Comp
open FStar.Relational

assume val iNLINE : #a:Type -> a -> a

(* Careful with these... They imply False *)
assume val l_PROJECT : #a:Type -> #b:Type -> a -> b
assume val r_PROJECT : #a:Type -> #b:Type -> a -> b

assume type l_PROJECT_TYP: Type -> Type
assume type r_PROJECT_TYP: Type -> Type

type sem_equiv (t:Type) = unit -> ST2 (double t) 
                                      (requires (fun h -> equal (R.l h) (R.r h)))
                                      (ensures  (fun h1 r h2 -> (equal (R.l h2) (R.r h2)) /\ (R.l r) = (R.r r)))

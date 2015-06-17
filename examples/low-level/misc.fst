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



(*copied fro examples/maths/bijection.fst, because that file doesn't compile*)
type inverseLR (#a:Type) (#b:Type) (fab:(a -> Tot b)) (fba:(b -> Tot a)) =
       (forall (x:a). fba (fab x) = x) /\ (forall (y:b). fab (fba y) = y)

(*It should be possible to implement it using the existing assumptions in Heap,
    perhaps using Heap.restrict?
val freeRefInBlock : #a:Type -> r:(ref a) -> h:heap (*{Heap.contains h r} *) -> Tot heap
let freeRefInBlock r h = restrict h *)

(*it seems that F* does not have dependent records
type memRep (a:Type) = {sz:nat;  rep:a->Tot (l:list nat{length l=sz})}
*)
type word=int
(*it seems that F* does not have paremetrized inductive types.
    It has indexed inductive types, which is too powerful for defining the concept below;
    the definitions of members of the type family below do not depend on each other
    *)
type memRep : Type -> Type =
  | MkRep : #a:Type -> sz:nat
        -> rep:(a->Tot (l:list word{length l=sz}))
        -> repInv:((l:list word{length l=sz})-> Tot a){inverseLR repInv rep}
        -> memRep a

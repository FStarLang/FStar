(*--build-config
    options:--admit_fsi Set --z3timeout 10;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst  stack.fst listset.fst st3.fst $LIB/constr.fst word.fst
  --*)

module MVector
open StructuredMem
open MachineWord
open Heap
open Set
(*
    Can we generalize vector to cover all the algebraic types definable in C?
*)
type vector : Type -> nat -> Type

(*can we make them ghosts*)
val updateIndex : #a:Type -> #n:nat -> (vector a n)
  -> index:nat{index<n} -> a -> Tot (vector a n)

val atIndex : #a:Type -> #n:nat -> (vector a n)
  -> index:nat{index<n} -> Tot a


val readIndex :  #a:Type -> #n:nat -> r:(ref (vector a n))
  -> index:nat{index<n} -> PureMem a (fun m -> b2t (refExistsInMem r m)) (fun _ _ _-> True)

val subVector : #a:Type -> #n:nat -> offset:nat
  -> len:(k:nat{k+offset<n}) -> (vector a n) -> Tot (vector a len)


val updIndex :  #a:Type -> #n:nat -> r:(ref (vector a n))
  -> index:(index:nat{index<n}) -> newV:a ->
 Mem unit
    (requires (fun m -> b2t (refExistsInMem r m)))
    (ensures (fun m0 _ m1-> (refExistsInMem r m0) /\ m1= (writeMemAux r  m0 (updateIndex (loopkupRef r m0) index newV))))
    (singleton (Ref r))
(*There is no way to read or write a whole vector.

(Technically, you can read a vector, but there's nothing you can do with
  the result if updateIndex and atIndex are ghosts.)

This seems closer to C's lvalue/rvalue semantics.

If we allowed a program to read
 a full vector and apply some blackbox/convoluted function to it,
 and write it back, what would the compiler do?*)

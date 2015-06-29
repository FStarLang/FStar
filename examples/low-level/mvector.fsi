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
open Stack

(*
    Can we generalize vector to cover all the algebraic types definable in C?
*)
type vector : Type -> nat -> Type

(*can we make them ghosts*)
val updateIndex : #a:Type -> #n:nat -> (vector a n)
  -> index:nat{index<n} -> a -> Tot (vector a n)

val atIndex : #a:Type -> #n:nat -> (vector a n)
  -> index:nat{index<n} -> Tot a



val subVector : #a:Type -> #n:nat -> offset:nat
  -> len:(k:nat{k+offset<=n}) -> (vector a n) -> Tot (vector a len)

(*--build-config
    options:--admit_fsi Set --z3timeout 10;
    other-files:ext.fst set.fsi heap.fst st.fst list.fst  stack.fst listset.fst st3.fst constr.fst word.fst
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


type prefixEqual  (#a:Type) (#n1:nat) (#n2:nat)
  (v1: vector a n1) (v2: vector a n2) (p:nat{p <= n1 /\ p<= n2})
  = forall (n:nat). n<p ==> atIndex v1 n = atIndex v2 n

val subVector : #a:Type -> #n:nat -> offset:nat
  -> len:(k:nat{k+offset<=n}) -> (vector a n) -> Tot (vector a len)

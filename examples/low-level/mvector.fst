(*--build-config
    options:--admit_fsi Set --z3timeout 10;
    other-files:ext.fst set.fsi heap.fst st.fst list.fst  stack.fst listset.fst st3.fst constr.fst word.fst mvector.fsi
  --*)

(*rename mvector to vector. The word array is used for memory-stored vectors *)
module MVector
open StructuredMem
open MachineWord
open Heap
open Stack
open Set


type vector (a:Type) (n:nat) = (index:nat{index<n} -> Tot a)

val updateIndex : #a:Type -> #n:nat -> (vector a n)
  -> index:nat{index<n} -> a -> Tot (vector a n)
let updateIndex 'a #n f index newV indx =
  if (indx= index) then newV else f indx




val atIndex : #a:Type -> #n:nat -> (vector a n)
  -> index:nat{index<n} -> Tot a
let atIndex 'a #n f index  =
   f index

(* When F* complains that effect ALL and StSTATE cannot be combined,
  see whether you missed a Tot somewhere.
  Is there a way to make Tot the default effect, instead of ALL
*)

val subVector : #a:Type -> #n:nat -> offset:nat
  -> len:(k:nat{k+offset<=n}) -> (vector a n) -> Tot (vector a len)
let subVector 'a #n offset leng f indx =f (indx+offset)

(*--build-config
    options:--admit_fsi Set --z3timeout 10;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst  stack.fst listset.fst st3.fst $LIB/constr.fst word.fst mvector.fsi
  --*)

(*rename mvector to vector. The word array is used for memory-stored vectors *)
module MVector
open StructuredMem
open MachineWord
open Heap
open Stack
open Set


type vector (a:Type) (n:nat) = (index:nat{index<n} -> Tot a)

let updateIndex 'a #n f index newV indx =
  if (indx= index) then newV else f indx

let atIndex 'a #n f index  =
   f index

(* When F* complains that effect ALL and StSTATE cannot be combined,
  see whether you missed a Tot somewhere.
  Is there a way to make Tot the default effect, instead of ALL
*)

let subVector 'a #n offset leng f indx =f (indx+offset)

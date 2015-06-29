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

let readIndex 'a #n r index =
  let rv = (memread r) in (atIndex rv index)

let updIndex 'a #n r index newV =
  let rv = (memread r) in
  memwrite r (updateIndex rv index newV)

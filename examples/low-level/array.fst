(*--build-config
    options:--admit_fsi Set --z3timeout 10;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst  stack.fst listset.fst $LIB/constr.fst word.fst $LIB/seq.fsi $LIB/seq.fst  $LIB/ghost.fst stackAndHeap.fst sst.fst sstCombinators.fst array.fsi
  --*)

(*rename mvector to vector. The word array is used for memory-stored vectors *)
module SSTArray
open SSTCombinators
open StackAndHeap
open SST
open MachineWord
open Heap
open Stack
open Set
open Seq

type array (a:Type) = ref (seq a)


(*Can we reinclude the types here, even when they are included in .fsi?
  F* does not complain, even if we change the types*)
 (*val length : #a:Type -> (array a) -> Tot string
 let length v = "cat"*)

open Ghost
let asRef va = hide va

let readIndex 'a r index =
  let rv = (memread (r)) in (Seq.index rv index)

let writeIndex 'a r index newV =
  let rv = (memread (r) ) in
  memwrite (r) (Seq.upd rv index newV)

let screateSeq init = (salloc init)

let hcreateSeq init = (halloc init)

let screate len init = (salloc (Seq.create len init))

let hcreate len init = (halloc (Seq.create len init))

let to_seq  r = memread (r)

let length r = Seq.length (memread r)

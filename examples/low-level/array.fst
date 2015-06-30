(*--build-config
    options:--admit_fsi Set --z3timeout 10;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst  stack.fst listset.fst st3.fst $LIB/constr.fst word.fst $LIB/seq.fsi $LIB/seq.fst array.fsi
  --*)

(*rename mvector to vector. The word array is used for memory-stored vectors *)
module Array
open StructuredMem
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


(*val asRef : #a:Type  -> va:(array a) -> GTot (ref (vector a (length va)))*)
let asRef va = va

let readIndex 'a r index =
  let rv = (memread (r)) in (Seq.index rv index)

let writeIndex 'a r index newV =
  let rv = (memread (r) ) in
  memwrite (r) (Seq.upd rv index newV)

let screate  init = (salloc init)

let hcreate init = (halloc init)

let to_seq  r = memread (r)

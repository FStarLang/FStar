(*--build-config
    options:--admit_fsi Set --z3timeout 10;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst  stack.fst listset.fst st3.fst $LIB/constr.fst word.fst mvector.fsi mvector.fst array.fsi
  --*)

(*rename mvector to vector. The word array is used for memory-stored vectors *)
module Array
open StructuredMem
open MachineWord
open Heap
open Stack
open Set
open MVector

type array : Type -> Type =
 | MkArr : #a:Type -> len:nat -> ref:(ref (vector a len)) -> array a

(*Can we reinclude the types here, even when they are included in .fsi?
  F* does not complain, even if we change the types*)
 (*val length : #a:Type -> (array a) -> Tot string
 let length v = "cat"*)


(*val length : #a:Type -> (array a) -> Tot nat*)
let length v = MkArr.len v

(*val asRef : #a:Type  -> va:(array a) -> GTot (ref (vector a (length va)))*)
let asRef va = MkArr.ref va


let readIndex 'a r index =
  let rv = (memread (MkArr.ref r)) in (atIndex rv index)

let writeIndex 'a r index newV =
  let rv = (memread (MkArr.ref r) ) in
  memwrite (MkArr.ref r) (updateIndex rv index newV)


let screateArray #n  init =
  MkArr n (salloc init)

let hcreateArray #n init =
  MkArr n (halloc init)


let readArray  r = memread (MkArr.ref r)

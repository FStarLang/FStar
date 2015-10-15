(*--build-config
    options:--admit_fsi FStar.Set --z3timeout 10;
    other-files:ext.fst set.fsi heap.fst st.fst all.fst list.fst  stack.fst listset.fst constr.fst word.fst seq.fsi seq.fst  ghost.fst located.fst lref.fst stackAndHeap.fst sst.fst rstWhile.fst array.fsi
  --*)

(*rename mvector to vector. The word sstarray is used for memory-stored vectors *)
module FStar.Regions.RSTArray
open FStar.Regions.RSTWhile
open FStar.Regions.Regions  open FStar.Regions.Heap  open FStar.Regions.Located
open FStar.Regions.RST
open MachineWord
open FStar.Heap
open Stack
open FStar.Set
open FStar.Seq

type sstarray (a:Type) = lref (seq a)


(*Can we reinclude the types here, even when they are included in .fsi?
  F* does not complain, even if we change the types*)
 (*val length : #a:Type -> (sstarray a) -> Tot string
 let length v = "cat"*)

open FStar.Ghost
let asRef va = hide va

let readIndex 'a r index =
  let rv = (memread (r)) in (Seq.index rv index)

let writeIndex 'a r index newV =
  let rv = (memread (r) ) in
  memwrite (r) (Seq.upd rv index newV)

let screateSeq init = (ralloc init)

let hcreateSeq init = (halloc init)

let screate len init = (ralloc (Seq.create len init))

let hcreate len init = (halloc (Seq.create len init))

let to_seq  r = memread (r)

let length r = Seq.length (memread r)

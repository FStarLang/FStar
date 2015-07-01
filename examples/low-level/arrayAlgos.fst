(*--build-config
    options:--admit_fsi Set --z3timeout 10;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst  stack.fst listset.fst
    st3.fst $LIB/constr.fst word.fst $LIB/seq.fsi $LIB/seq.fst array.fsi array.fst withScope.fst
  --*)
module ArrayAlgos
open StructuredMem
open MVector
open Heap
open Set
open MachineWord
open Array
open MD5Common
open Seq

val contains : #a:Type -> smem -> array a -> GTot bool
let contains m v = refExistsInMem (asRef v) m

val sel : #a:Type -> m:smem -> v:(array a){contains m v} -> GTot (seq a)
let sel m v = loopkupRef (asRef v) m

val glength : #a:Type -> v:(array a) -> m:smem{contains m v} -> GTot nat
let glength v m = Seq.length (sel m v)

type prefixEqual  (#a:Type)
  (v1: seq a) (v2: seq a) (p:nat{p <= length v1 /\ p<= length v2})
  = forall (n:nat{n<p}). index v1 n = index v2 n

(*val prefixInc: a#Type -> n:nat->
  (m1 = (writeMemAux (asRef r) m0 (Seq.upd (loopkupRef (asRef r) m0) index newV)))*)

type prefixEqualL  (#a:Type)
  (v1: seq a) (v2:(seq a))
  = length v1 <= length v2 /\ (forall (n:nat{n<length v1}). index v1 n = index v2 n)


(* Helper functions for stateful array manipulation *)
val copy:
  #a:Type -> s:array a -> scp :array a
  -> WNSC unit
     (requires (fun h -> contains h s /\ contains h scp /\ glength s h <= glength scp h))
     (ensures (fun h0 _ h1 -> (contains h1 s) /\  (contains h1 scp)
                /\ (glength  s h1  <= glength  scp h1)
                /\ prefixEqualL (sel h1 s) (sel h1 scp)
                /\ (contains h0 scp) /\ glength scp h0 = glength scp h1
              ))
     (only (asRef scp))

let copy s scp =
  let ctr = salloc #nat 0 in
  let len = Array.length s in
  let lenscp = Array.length scp in
  scopedWhile1
    ctr
    (fun ctrv -> ctrv < len)
    (fun m -> contains m s /\ contains m scp
        /\ len = glength s m /\ lenscp = glength scp m
          /\ refExistsInMem ctr m
          /\ (loopkupRef ctr m) <=len
          /\ prefixEqual (sel m s) (sel m scp) (loopkupRef ctr m)
          )
    (union (only (asRef scp)) (only ctr))
    (fun u -> let ctrv = memread ctr in
              writeIndex scp ctrv (readIndex s ctrv);
              memwrite ctr (ctrv +1 ))

(* sclone does not make sense*)
val hcloneAux:
  #a:Type -> s:array a
  -> Mem (array a)
     (requires (fun h -> contains h s /\ 0 < glength s h ))
     (ensures (fun h0 scp h1 -> (contains h1 s) /\  (contains h1 scp)
                /\ (glength s h1) = (glength scp h1)
                /\ Seq.Eq (sel h1 s) (sel h1 scp)
              ))
     (empty)

let hcloneAux s =
  let scp = hcreate (Seq.create (Array.length s) (readIndex s 0)) in
    pushStackFrame ();
      copy s scp;
    popStackFrame ();
    scp

(*Since we always use the Mem abbreviation and never SST directly,
  withNewScope does not have any advantage over pushStackFrame/popStackFrame.
  The definition of Mem prevents one from improperly pushing/popping
    of stack frames; i.e. any computation of type Mem ....
    must pop exactly all the stack frames it pushed
  *)

    (*let hcloneAux s =
      let scp = hcreate (Seq.create (Array.length s) (readIndex s 0)) in
        withNewScope
          #_ (*the pre/post conditions below just come from the definition of copy. It is annoying that they cannot be inferred*)
          #((fun h -> contains h s /\ contains h scp /\ glength s h <= glength scp h))
          #((fun h0 _ h1 -> (contains h1 s) /\  (contains h1 scp)
                   /\ (glength  s h1  <= glength  scp h1)
                   /\ prefixEqualL (sel h1 s) (sel h1 scp)
                   /\ (contains h0 scp) /\ glength scp h0 = glength scp h1
                 ))
          #(only (asRef scp))
          (fun u -> copy s scp);
        scp*)



(*allow creation of uninitialized arrays? ,
  but use the type system to prevent reading of uninitialized indices?

  Currently, there might be some wasted computation in initializing an array
  that will immediately be written into.
*)


val hclone:
  #a:Type -> s:array a
  -> Mem (array a)
     (requires (fun h -> contains h s))
     (ensures (fun h0 scp h1 -> (contains h1 s) /\  (contains h1 scp)
                /\ (glength s h1) = (glength scp h1)
                /\ Seq.Eq (sel h1 s) (sel h1 scp)
              ))
     (empty)

let hclone 'a s =
  if (Array.length s = 0)
  then  hcreate (Seq.createEmpty #'a)
  else hcloneAux s

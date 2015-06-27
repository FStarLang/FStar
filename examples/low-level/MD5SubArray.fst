(*--build-config
    options:--admit_fsi Set --z3timeout 50;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst  stack.fst listset.fst
    st3.fst $LIB/constr.fst word.fst mvector.fsi mvector.fst MD5.fst
  --*)

(*Why is MD5 so? Why did its designer(s) think
  it was a good way to convolute bits?
  Is there a principle behind its design? or just random convolutery?
  *)
module MD5SubArray
open StructuredMem
open MVector
open Heap
open Set
open MachineWord
open MD5

type array (a:Type) (n:nat)= vector (ref a) n

type chunk512 = array word 16

type arrayExixtsInMem (#a:Type) (#n:nat) (v: array a n) (m:smem) =
  forall (k:(p:nat{p<n})).{:pattern(k<n)} refExistsInMem (atIndex v k) m

val flattenRefsUpto : #a:Type -> #n:nat -> upto:(m:nat{m<=n}) -> (array a n) -> Tot (set aref)
let rec flattenRefsUpto 'a #n upto v  =
  match upto with
  | 0 -> empty
  | _ -> union (singleton (Ref (atIndex v (upto-1)))) (flattenRefsUpto (upto -1) v)


val flattenRefs : #a:Type -> #n:nat -> (array a n) -> Tot (set aref)
let flattenRefs 'a #n v  = flattenRefsUpto n v


val processChunkSubArray :
 ch:chunk512
-> acc:(array word 4)
-> WNSC unit
    (fun m -> arrayExixtsInMem ch m
              /\ arrayExixtsInMem acc m
                (*/\ ch =!= acc : why was this not needed?*)
              )
    (fun _ _ m1 -> arrayExixtsInMem ch m1
              /\ arrayExixtsInMem acc m1
              (*/\ ch =!= acc*)
              )
    ((flattenRefs acc))

(*had to increase timeout to get this to typecheck.
  The switch from "ref vector" to "vector ref" cost atleast 10 times more time
*)
let processChunkSubArray ch acc =
  let li = salloc #nat 0 in
  scopedWhile1
    li
    (fun liv -> liv < 64)
    (fun m -> True
              /\ arrayExixtsInMem ch m
              /\ arrayExixtsInMem acc m
              /\ refExistsInMem li m /\ loopkupRef li m < 65
              )
    (union (singleton (Ref li)) (flattenRefs acc))
    (*allRefs ; why does this not work?*)
    (fun u ->
      let liv = memread li in
      let vA = memread (atIndex acc iA) in
      let vB = memread (atIndex acc iB) in
      let vC = memread (atIndex acc iC) in
      let vD = memread (atIndex acc iD) in
      let fF:word = funFGHI liv vB vC vD in
      let g:(n:nat{n<16}) = idx liv liv in
      memwrite (atIndex acc iD) vC;
      memwrite (atIndex acc iA) vD;
      let mg = memread  (atIndex ch g) in
      let vBr = wmodAdd vA  (wmodAdd fF ( wmodAdd(consts liv)  mg)) in
      memwrite (atIndex acc iB) (wmodAdd vB (leftrotate (rots liv) vBr));
      memwrite li (liv+1)

      )

(*--build-config
    options: --codegen OCaml-experimental --trace_error --debug yes --prn;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/set.fst $LIB/heap.fst $LIB/st.fst $LIB/list.fst  stack.fst listset.fst
    $LIB/ghost.fst stackAndHeap.fst sst.fst sstCombinators.fst $LIB/constr.fst word.fst $LIB/seq.fsi $LIB/seq.fst array.fsi
     array.fst MD5Common.fst arrayAlgos.fst
  --*)

(*Why is MD5 so? Why did its designer(s) think
  it was a good way to convolute bits?
  Is there a principle behind its design? or just random convolutery?
  *)
module MD5
open SSTCombinators
open StackAndHeap
open SST
open MVector
open Heap
open Set
open MachineWord
open Array
open MD5Common
open ArrayAlgos
open Seq
open Ghost

assume val cloneAndPad :
  r:(array word)
  -> rcloned :(array word)
  -> Mem unit
      (fun m -> refExistsInMem (reveal (asRef r)) m /\ refExistsInMem (reveal (asRef rcloned)) m)
      (fun m0 rp m1  -> refExistsInMem (reveal (asRef r)) m0 /\ refExistsInMem (reveal (asRef rcloned)) m1
          /\ refExistsInMem (reveal (asRef r)) m1
          /\ Seq.length (loopkupRef (reveal (asRef rcloned)) m1) = psize (Seq.length (loopkupRef (reveal (asRef r)) m0))
          /\ prefixEqual
                (loopkupRef (reveal (asRef r)) m0)
                (loopkupRef (reveal (asRef rcloned)) m1)
                (Seq.length (loopkupRef (reveal (asRef r)) m0)))
        (hide empty)

val processChunk :
 ch:(array word)
 -> offset:nat
 -> acc:(array word)
 -> WNSC unit
    (requires (fun m -> refExistsInMem (reveal (asRef ch)) m
              /\ refExistsInMem (reveal (asRef acc)) m /\ ch =!= acc
              /\ offset + 16 <= (Seq.length (loopkupRef (reveal (asRef ch)) m))
              /\ 4 = (length (loopkupRef (reveal (asRef acc)) m))
              ))
    (ensures (fun m0 _ m1 -> refExistsInMem (reveal (asRef ch)) m1
              /\ refExistsInMem (reveal (asRef acc)) m1 /\ ch =!= acc
              /\ 4 = (Seq.length (loopkupRef (reveal (asRef acc)) m1))
              (*/\ loopkupRef  ch m0 = loopkupRef ch m1*)
              ))
    (eonly ((asRef acc)))


let processChunk ch offset acc =
  let li = salloc #nat 0 in
  scopedWhile1
    li
    (fun liv -> liv < 64)
    (fun m -> True
              /\ refExistsInMem (reveal (asRef ch)) m
              /\ refExistsInMem (reveal (asRef acc)) m
              /\ offset + 16 <= (Seq.length (loopkupRef (reveal (asRef ch)) m))
              /\ 4 = (length (loopkupRef (reveal (asRef acc)) m))
              /\ refExistsInMem li m /\ loopkupRef li m < 65
              )
    ((elift2 union) (gonly li) (eonly (asRef acc)))
    (*allRefs ; why does this not work?*)
    (fun u ->
      let liv = memread li in
      let vA = readIndex acc iA in
      let vB = readIndex acc iB in
      let vC = readIndex acc iC in
      let vD = readIndex acc iD in
      let fF:word = funFGHI liv vB vC vD in
      let g:(n:nat{n<16}) = idx liv liv in
      writeIndex acc iD vC;
      writeIndex acc iA vD;
      let mg = readIndex ch (offset+g) in
      let vBr = wmodAdd vA  (wmodAdd fF ( wmodAdd(consts liv)  mg)) in
      writeIndex acc iB (wmodAdd vB (leftrotate (rots liv) vBr));
      memwrite li (liv+1))

val mainLoop :
 ch:(array word)
 -> un:unit
 -> WNSC (s:(seq word){Seq.length s = 4})
    (requires (fun m -> refExistsInMem (reveal (asRef ch)) m
          /\ divides 16 (Seq.length (loopkupRef (reveal (asRef ch)) m))))
    (ensures (fun m0 _ m1 -> True /\ refExistsInMem (reveal (asRef ch)) m1))
    (hide empty)

let mainLoop ch u =
  let offset = salloc #nat 0 in
  let acc =  screate initAcc in
  let chl = Array.length ch in
  scopedWhile1
    offset
    (fun offsetv-> offsetv +16 <= chl)
    (fun m -> True
              /\ refExistsInMem (reveal (asRef ch)) m
              /\ refExistsInMem (reveal (asRef acc)) m
              /\ refExistsInMem offset m
              /\ Seq.length (loopkupRef (reveal (asRef ch)) m) = chl
              /\ 4 = (Seq.length (loopkupRef (reveal (asRef acc)) m))
              )
    ((elift2 union) (gonly  offset) (eonly (asRef acc)))
    (fun u ->
        let offsetv = memread offset in
        processChunk ch offsetv acc;
        memwrite offset (offsetv + 16));
  (to_seq acc)

val allZeros : n:nat -> Tot (s:(seq word){length s = n})
let allZeros n = Seq.create n w0

val mD5 :
 ch:(array word)
 -> WNSC (s:(seq word){Seq.length s = 4})
    (fun m -> True /\ refExistsInMem (reveal (asRef ch)) m)
    (fun m0 _ m1 -> True /\ refExistsInMem (reveal (asRef ch)) m1)
    (hide empty)

let mD5 ch =
  let chl = Array.length ch in
  let clonedCh = screate (allZeros (psize chl)) in
  cloneAndPad ch clonedCh;
  withNewScope
    #_
    #(fun m -> refExistsInMem (reveal (asRef ch)) (m) /\ refExistsInMem (reveal (asRef clonedCh)) (m)
        /\ divides 16 (Seq.length (loopkupRef (reveal (asRef clonedCh)) m)) )
    #(fun m0 _ m1 -> True /\ refExistsInMem (reveal (asRef ch)) (m1))
    #(hide empty)
    (mainLoop clonedCh)

(*open Example2

val mD53 : n:nat
 -> ch:(array word)
 -> WNSC (vector word 4)
    (fun m -> True /\ refExistsInMem (asRef ch) m)
    (fun m0 _ m1 -> True /\ refExistsInMem (asRef ch) m1)
    (empty)

let mD53 n ch =
  let clonedCh = screateArray (allZeros (psize n)) in
  cloneAndPad ch clonedCh;
  withNewScope4
    (mainLoop clonedCh)*)


val mD52 : n:nat
 -> ch:(array word)
 -> WNSC  (s:(seq word){Seq.length s = 4})
    (fun m -> True /\ refExistsInMem (reveal (asRef ch)) m)
    (fun m0 _ m1 -> True /\ refExistsInMem (reveal (asRef ch)) m1)
    (hide empty)

let mD52 n ch =
  let clonedCh = screate (allZeros (psize n)) in
  cloneAndPad ch clonedCh;
    pushStackFrame ();
      let mdd5 = mainLoop clonedCh () in
    popStackFrame (); mdd5


(*can we run this program and compare it agains standard implementations?
  That at least needs the following:
  1) implementations of admitted functions, e.g. padding
  2) implementations of =
  3) (optionally, for efficiency) proper "Extraction" of word to native words in OCaml
*)

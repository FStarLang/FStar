(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
(*Why is MD5 so? Why did its designer(s) think
  it was a good way to convolute bits?
  Is there a principle behind its design? or just random convolutery?
  *)
module MD5
open FStar.Regions.RSTWhile
open FStar.Regions.RST
open MVector
open Set
open MachineWord
open MD5Common
open StackAndHeap
open FStar.Regions.Heap  open FStar.Regions.Located
open Seq
open FStar.Regions.RSTArray
open ArrayAlgos
open Ghost


assume val cloneAndPad :
  r:(sstarray word)
  -> rcloned :(sstarray word)
  -> Mem unit
      (fun m -> (liveArr m r) /\ (liveArr m rcloned))
      (fun m0 rp m1  -> (liveArr m0 r) /\ (liveArr m1 rcloned)
          /\ (liveArr m1 r)
          /\ (glength rcloned m1) = psize ((glength r m0))
          /\ prefixEqual
                (lookupRef (reveal (asRef r)) m0)
                (lookupRef (reveal (asRef rcloned)) m1)
                ((glength r m0)))
        (hide empty)

val processChunk :
 ch:(sstarray word)
 -> offset:nat
 -> acc:(sstarray word)
 -> WNSC unit
    (requires (fun m -> (liveArr m ch)
              /\ (liveArr m acc) /\ ch =!= acc
              /\ offset + 16 <= ((glength ch m))
              /\ 4 = ((glength acc m))
              ))
    (ensures (fun m0 _ m1 -> (liveArr m1 ch)
              /\ (liveArr m1 acc) /\ ch =!= acc
              /\ 4 = ((glength acc m1))
              (*/\ lookupRef  ch m0 = lookupRef ch m1*)
              ))
    (eonly acc)


let processChunk ch offset acc =
  let li = ralloc #nat 0 in
  scopedWhile1
    li
    (fun liv -> liv < 64)
    (fun m -> True
              /\ (liveArr m ch)
              /\ (liveArr m acc)
              /\ offset + 16 <= ((glength ch m))
              /\ 4 = ((glength acc m))
              /\ refIsLive li m /\ lookupRef li m < 65
              )
    (eunion (only li) (eonly acc))
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
 ch:(sstarray word)
 -> un:unit
 -> WNSC (s:(seq word){Seq.length s = 4})
    (requires (fun m -> (liveArr m ch)
          /\ divides 16 ((glength ch m))))
    (ensures (fun m0 _ m1 -> True /\ (liveArr m1 ch)))
    (hide empty)

let mainLoop ch u =
  let offset = ralloc #nat 0 in
  let acc =  screateSeq initAcc in
  let chl = FStar.Regions.RSTArray.length ch in
  scopedWhile1
    offset
    (fun offsetv-> offsetv +16 <= chl)
    (fun m -> True
              /\ (liveArr m ch)
              /\ (liveArr m acc)
              /\ refIsLive offset m
              /\ (glength ch m) = chl
              /\ 4 = ((glength acc m))
              )
    (eunion (only  offset) (eonly acc))
    (fun u ->
        let offsetv = memread offset in
        processChunk ch offsetv acc;
        memwrite offset (offsetv + 16));
  (to_seq acc)

val allZeros : n:nat -> Tot (s:(seq word){Seq.length s = n})
let allZeros n = Seq.create n w0

val mD5 :
 ch:(sstarray word)
 -> WNSC (s:(seq word){Seq.length s = 4})
    (fun m -> True /\ (liveArr m ch))
    (fun m0 _ m1 -> True /\ (liveArr m1 ch))
    (hide empty)

let mD5 ch =
  let chl = FStar.Regions.RSTArray.length ch in
  let z:nat =0 in
  let clonedCh = screate  (psize chl) w0 in
  cloneAndPad ch clonedCh;
  withNewScope
    #_
    #(fun m -> (liveArr m ch) /\ (liveArr m clonedCh)
        /\ divides 16 ((glength clonedCh m)) )
    #(fun m0 _ m1 -> True /\ liveArr m1 ch)
    #(hide empty)
    (mainLoop clonedCh)

(*open Example2

val mD53 : n:nat
 -> ch:(sstarray word)
 -> WNSC (vector word 4)
    (fun m -> True /\ refIsLive (asRef ch) m)
    (fun m0 _ m1 -> True /\ refIsLive (asRef ch) m1)
    (empty)

let mD53 n ch =
  let clonedCh = screateArray (allZeros (psize n)) in
  cloneAndPad ch clonedCh;
  withNewScope4
    (mainLoop clonedCh)*)


val mD52 : n:nat
 -> ch:(sstarray word)
 -> WNSC  (s:(seq word){Seq.length s = 4})
    (fun m -> True /\ (liveArr m ch))
    (fun m0 _ m1 -> True /\ (liveArr m1 ch))
    (hide empty)

let mD52 n ch =
  let clonedCh = screate (psize n) w0 in
  cloneAndPad ch clonedCh;
    pushRegion ();
      let mdd5 = mainLoop clonedCh () in
    popRegion (); mdd5


(*can we run this program and compare it against standard implementations?
  That at least needs the following:
  1) implementations of admitted functions, e.g. padding
  2) implementations of =
  3) (optionally, for efficiency) proper "Extraction" of word to native words in OCaml
*)

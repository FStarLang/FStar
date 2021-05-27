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
module Demo
open FStar.HyperStack.ST
open LowStar.Buffer
open Demo.Deps

(**
    A demo of F*, Low* and KreMLin
    Copying a buffer of bytes 
**)

/// Attempt: copy just the first byte
[@@expect_failure [19]] //liveness
let copy0 (src dest:buffer uint8) : St unit =
  dest.(0ul) <- src.(0ul)


/// Attempt: copy just the first byte, but add a bounds check
[@@expect_failure] //bounds check
let copy1 (len:uint32) (src dest:lbuffer len uint8) 
  : ST unit
       (requires fun h ->
         live h src /\
         live h dest)
       (ensures fun h0 _ h1 ->
         modifies dest h0 h1)
  = dest.(0ul) <- src.(0ul)

/// Copy just the first byte, but add both a bounds check
/// and a liveness pre-condition
///    -- No out of bounds memory access
///    -- No use after free
let copy2 (len:uint32) (src dest:lbuffer len uint8)
  : ST unit 
       (requires fun h ->
         live h src /\
         live h dest)
       (ensures fun h0 _ h1 ->
         modifies dest h0 h1)
  = if 0ul < len
    then dest.(0ul) <- src.(0ul)


/// Copy the entire buffer, in a recursive function
let rec copy3
        (len:uint32)
        (cur:uint32{cur <= len})
        (src dest:lbuffer len uint8)
  : ST unit 
       (requires fun h ->
         live h src /\
         live h dest)
       (ensures fun h0 _ h1 ->
         modifies dest h0 h1)
  = if cur < len
    then begin
      dest.(cur) <- src.(cur);
      copy3 len (cur + 1ul) src dest
    end

/// Attempt: Prove the copy correct
///     -- Needs a loop invariant
[@@expect_failure] //not inductive
let rec copy4
        (len:uint32)
        (cur:uint32{cur <= len})
        (src dest:lbuffer len uint8)
  : ST unit 
       (requires fun h ->
         live h src  /\
         live h dest /\
         prefix_equal h src dest cur)
       (ensures fun h0 _ h1 ->
         modifies dest h0 h1 /\
         prefix_equal h1 src dest len)
  = if cur < len
    then begin
      dest.(cur) <- src.(cur);
      copy4 len (cur + 1ul) src dest
    end


/// Attempt: Prove the copy correct
///     -- Needs a loop invariant
let rec memcpy
        (len:uint32)
        (cur:uint32{cur <= len})
        (src dest:lbuffer len uint8)
  : ST unit 
       (requires fun h ->
         live h src  /\
         live h dest /\
         disjoint src dest /\
         prefix_equal h src dest cur)
       (ensures fun h0 _ h1 ->
         modifies dest h0 h1 /\
         prefix_equal h1 src dest len)
  = if cur < len
    then begin
      dest.(cur) <- src.(cur);
      memcpy len (cur + 1ul) src dest
    end

let malloc_copy_free (len:uint32 { 0ul < len })
                    (src:lbuffer len uint8)
  : ST (lbuffer len uint8)
       (requires fun h -> 
         live h src /\
         freeable src)
       (ensures fun h0 dest h1 -> 
         live h1 dest /\
         (forall (j:uint32). j < len ==> get h0 src j
                                 == get h1 dest j))
  = let dest = malloc 0uy len in
    memcpy len 0ul src dest;
    free src;
    dest

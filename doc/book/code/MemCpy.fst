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
module MemCpy
open FStar.HyperStack.ST
open LowStar.Buffer
open MemCpy.Deps

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

//SNIPPET_START: malloc_copy_free
let malloc_copy_free (len:uint32 { 0ul < len })
                     (src:lbuffer len uint8)
  : ST (lbuffer len uint8)
       (requires fun h -> 
         live h src /\
         freeable src)
       (ensures fun h0 dest h1 -> 
         live h1 dest /\
         (forall (j:uint32). j < len ==> get h0 src j == get h1 dest j))
  = let dest = malloc 0uy len in
    memcpy len 0ul src dest;
    free src;
    dest
//SNIPPET_END: malloc_copy_free

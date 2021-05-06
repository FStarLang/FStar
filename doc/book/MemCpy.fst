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
open Demo.Deps

(**
    A demo of F*, Low* and KreMLin
    Copying a buffer of bytes 
**)


// SNIPPET_START: memcpy
(* 
   ``memcpy len src cur `` is an imperative procecdure
    to copy the contents of the ``src`` array into ``dest``
*)
let rec memcpy
        (len:uint32) //a 32-bit unsigned integero
        (cur:uint32{cur <= len}) //current position cur is no more than len
        (src dest:larray len uint8) //two arrays whose length is len
  : ST unit //A stateful computation, that can read, write, allocate or free memory
       (requires fun h -> //with a precondition on the initial state h
         live h src  /\ //expects src to be live
         live h dest /\ //expects dest to be live
         disjoint src dest /\ //and the two do not overlap in memory
         prefix_equal h src dest cur) //their contents are initially equal up to cur
       (ensures fun h0 _ h1 -> //and a postcondition relating their initial and final states
         modifies1 dest h0 h1 /\ //modifies only the dest array
         prefix_equal h1 src dest len) //and src and dest are equal up to len
  = (* The implementation of the function begins here *)
    if cur < len
    then (
      dest.(cur) <- src.(cur); //copy the cur byte
      memcpy len (cur + 1ul) src dest //recurse
    )
// SNIPPET_END: memcpy

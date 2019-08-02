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
module ExtractionExamples

open FStar.Buffer
open FStar.HyperStack
open FStar.HyperStack.ST
open C.Loops

module U32 = FStar.UInt32

// simple for loop example - note that there is no framing
let sum_to_n (n:U32.t) : Stack U32.t
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> r == n)) =
  push_frame();
  let ptr_sum = create 0ul 1ul in
  let _ = interruptible_for 0ul n
    (fun h i done -> live h ptr_sum /\
                  U32.v (Seq.index (as_seq h ptr_sum) 0) == i /\
                  done == false)
    (fun i -> ptr_sum.(0ul) <- U32.(ptr_sum.(0ul) +^ 1ul);
           false) in
  let sum = ptr_sum.(0ul) in
  pop_frame();
  sum

// verify the framing of a function that uses a stack-allocated buffer but
// eventually de-allocates it
let update_local (u:unit) : Stack unit
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> modifies_none h0 h1))=
  let h0 = get() in
  push_frame();
  let h1 = get() in
  let b = create 0ul 1ul in
  Buffer.upd b 0ul 5ul;
  let h2 = get() in
  pop_frame();
  let h3 = get() in
  lemma_modifies_0_push_pop h0 h1 h2 h3;
  ()

let sum_to_n_buf (n:U32.t) : Stack U32.t
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> r == n /\
    modifies_none h0 h1)) =
  push_frame();
  let h0 = get() in
  let ptr_sum = create 0ul 1ul in
  let _ = interruptible_for 0ul n
    (fun h i done -> live h ptr_sum /\
                  U32.v (Seq.index (as_seq h ptr_sum) 0) == i /\
                  done == false /\
                  modifies_0 h0 h)
    (fun i -> ptr_sum.(0ul) <- U32.(ptr_sum.(0ul) +^ 1ul);
           false) in
  let sum = ptr_sum.(0ul) in
  let h1 = get() in
  lemma_reveal_modifies_0 h0 h1;
  pop_frame();
  sum

let count_to_n (n:U32.t{U32.v n > 0}) : Stack U32.t
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> r == n)) =
  push_frame();
  let ptr_count = create 0ul 1ul in
  do_while
    (fun h break -> live h ptr_count /\
                 (not break ==> U32.v (Seq.index (as_seq h ptr_count) 0) < U32.v n) /\
                 (break ==> U32.v (Seq.index (as_seq h ptr_count) 0) == U32.v n))
    (fun _ -> ptr_count.(0ul) <- U32.(ptr_count.(0ul) +^ 1ul);
           let sum = ptr_count.(0ul) in
           if U32.eq sum n then true else false);
  let count = ptr_count.(0ul) in
  pop_frame();
  count

// this is just an infinite loop
let wait_for_false (n:U32.t{U32.v n > 0}) : Stack U32.t
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> r == n)) =
  push_frame();
  let ptr_count = create 0ul 1ul in
  do_while
    (fun h break -> live h ptr_count /\
                 (break ==> False))
    (fun _ -> false);
  let count = ptr_count.(0ul) in
  pop_frame();
  assert (False);
  count

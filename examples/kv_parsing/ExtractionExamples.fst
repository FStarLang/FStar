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

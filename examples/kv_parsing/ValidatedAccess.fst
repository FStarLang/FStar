module ValidatedAccess

open KeyValue
open PureParser
open Validator
open ValidatedParser
open Slice

open FStar.Seq
module List = FStar.List.Tot
open FStar.HyperStack
open FStar.HyperStack.ST
open C.Loops

module B = FStar.Buffer

module U16 = FStar.UInt16
module U32 = FStar.UInt32

(*** API to access validated but unparsed key-value buffer *)

(* Implementing lookup as a for loop *)

#reset-options "--z3rlimit 10"

// attempt to allow more general invariants in for_readonly
(*
val for_readonly :
  #t:Type0 ->
  init:t ->
  start:U32.t ->
  finish:U32.t{U32.v finish >= U32.v start} ->
  inv:(mem -> nat -> t -> bool -> GTot Type0){forall h h' i v break. (inv h i v break /\ modifies_none h h') ==> inv h' i v break} ->
  f:(i:U32.t{U32.(v start <= v i /\ v i < v finish)} -> v:t -> Stack (t * bool)
     (requires (fun h0 -> poppable h0 /\ inv (pop h0) (U32.v i) v false))
     (ensures (fun h0 r h1 -> let (v', break) = r in
                           poppable h0 /\
                           poppable h1 /\
                           inv (pop h0) (U32.v i) v false /\
                           inv (pop h1) U32.(v i + 1) v' break /\
                           modifies_none h0 h1))) ->
  Stack (U32.t * t * bool)
    (requires (fun h0 -> inv h0 (U32.v start) init false))
    (ensures (fun h0 r h1 -> let (i, v, break) = r in
                          (not break ==> i == finish) /\
                          inv h1 (U32.v i) v break /\
                          modifies_none h0 h1))
let for_readonly #t init start finish inv f =
  let h0 = get() in
  push_frame();
  let h1 = get() in
  let ptr_state = B.create #t init 1ul in
  assert (ptr_state `B.unused_in` h1 /\
          B.frameOf ptr_state == h1.tip);
  let h = get() in
  lemma_pop_is_popped h;
  B.lemma_modifies_0_push_pop h0 h1 h (pop h);
  let (i, break) = begin
    interruptible_for start finish
    (fun h i break ->
      B.live h ptr_state /\
      poppable h /\
      B.modifies_0 h1 h /\
      modifies_none h0 (pop h) /\
      inv (pop h) i (Seq.index (B.as_seq h ptr_state) 0) break)
    (fun i -> let h0' = get() in
           let v = B.index ptr_state 0ul in
           let (v', break) = f i v in
           let h1' = get() in
           B.upd ptr_state 0ul v';
           let h2' = get() in
           lemma_modifies_none_1_trans ptr_state h0' h1' h2';
           lemma_modifies_0_unalloc ptr_state h1 h0' h2';
           B.lemma_modifies_0_push_pop h0 h1 h (pop h);
           assume (modifies_none (pop h1') (pop h2'));
           admit();
           break)
    end in
  let v = B.index ptr_state 0ul in
  let h2 = get() in
  pop_frame();
  let h3 = get() in
  (i, v, break)
*)


// sadly for_readonly only takes a single buffer and we need two input buffers here
val for_readonly2 :
  #t:Type0 ->
  init:t ->
  start:U32.t ->
  finish:U32.t{U32.v finish >= U32.v start} ->
  #a1:Type ->
  // buf is logical; it can be captured by f at runtime
  buf1:B.buffer a1 ->
  #a2:Type ->
  buf2:B.buffer a2 ->
  inv:(vs1:seq a1{length vs1 == B.length buf1} ->
       vs2:seq a2{length vs2 == B.length buf2} ->
       nat -> t -> bool -> GTot Type0) ->
  f:(i:U32.t{U32.(v start <= v i /\ v i < v finish)} -> v:t -> Stack (t * bool)
     (requires (fun h0 -> B.live h0 buf1 /\
                       B.live h0 buf2 /\
                       inv (B.as_seq h0 buf1) (B.as_seq h0 buf2) (U32.v i) v false))
     (ensures (fun h0 r h1 -> let (v', break) = r in
                           B.live h0 buf1 /\
                           B.live h0 buf2 /\
                           B.live h1 buf1 /\
                           B.live h1 buf2 /\
                           inv (B.as_seq h0 buf1) (B.as_seq h0 buf2) (U32.v i) v false /\
                           inv (B.as_seq h1 buf1) (B.as_seq h1 buf2) U32.(v i + 1) v' break /\
                           modifies_none h0 h1))) ->
  Stack (U32.t * t * bool)
    (requires (fun h0 -> B.live h0 buf1 /\
                      B.live h0 buf2 /\
                      inv (B.as_seq h0 buf1) (B.as_seq h0 buf2) (U32.v start) init false))
    (ensures (fun h0 r h1 -> let (i, v, break) = r in
                          (not break ==> i == finish) /\
                          B.live h1 buf1 /\
                          B.live h1 buf2 /\
                          inv (B.as_seq h1 buf1) (B.as_seq h1 buf2) (U32.v i) v break /\
                          modifies_none h0 h1))
let for_readonly2 #t init start finish #a1 buf1 #a2 buf2 inv f =
  let h0 = get() in
  push_frame();
  let h1 = get() in
  let ptr_state = B.create #t init 1ul in
  assert (ptr_state `B.unused_in` h1 /\
          B.frameOf ptr_state == h1.tip);
  let h = get() in
  let (i, break) = begin
    interruptible_for start finish
    (fun h i break ->
      B.live h buf1 /\
      B.live h buf2 /\
      B.live h ptr_state /\
      B.modifies_0 h1 h /\
      inv (B.as_seq h buf1) (B.as_seq h buf2) i (Seq.index (B.as_seq h ptr_state) 0) break)
    (fun i -> let h0' = get() in
           let v = B.index ptr_state 0ul in
           let (v', break) = f i v in
           let h1' = get() in
           B.upd ptr_state 0ul v';
           let h2' = get() in
           lemma_modifies_none_1_trans ptr_state h0' h1' h2';
           lemma_modifies_0_unalloc ptr_state h1 h0' h2';
           break)
    end in
  let v = B.index ptr_state 0ul in
  let h2 = get() in
  pop_frame();
  let h3 = get() in
  B.lemma_modifies_0_push_pop h0 h1 h2 h3;
  (i, v, break)

val lookup : s:store -> key:bytes -> option bytes
let lookup s key =
  let rec aux (es:list encoded_entry) : option bytes =
  begin
    match es with
    | [] -> None
    | e::es -> if e.key = key then Some e.value
             else aux es
   end in
   aux s.entries

val lookup_st : input:bslice -> key:bslice -> Stack (option bslice)
  (requires (fun h0 -> live h0 input /\
                    live h0 key /\
                    (let bs = as_seq h0 input in
                    Some? (parse_abstract_store bs))))
  (ensures (fun h0 r h1 -> live h1 input /\
                        live h1 key /\
                        modifies_none h0 h1 /\
                        (let bs = as_seq h1 input in
                         let key_bs = as_seq h1 key in
                        Some? (parse_abstract_store bs) /\
                        (let s = parse_result (parse_abstract_store bs) in
                         match r with
                         | Some v_slice -> live h1 v_slice /\
                                          lookup s key_bs == Some (as_seq h1 v_slice)
                         | None -> lookup s key_bs == None))))
let lookup_st input key =
  let (num_entries, off) = parse_num_entries_valid input in
  let input = advance_slice input off in
  admit();
  None

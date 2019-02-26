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
(*
 *  The rest of the file provides a standalone Poly1305 MAC function proven
 *  functionally correct using an ideal log passed explicitly.
 *  It is not used in the Chacha20-Poly1305 AEAD construction.
 *)

module Crypto.Symmetric.Poly1305.Standalone

open FStar.Mul
open FStar.Seq
open FStar.Buffer

open Crypto.Symmetric.Bytes

open Crypto.Symmetric.Poly1305
open Crypto.Symmetric.Poly1305.Spec
open Crypto.Symmetric.Poly1305.Parameters
open Crypto.Symmetric.Poly1305.Bigint
open Crypto.Symmetric.Poly1305.Bignum
open Flag

module U32 = FStar.UInt32

let log_t = if mac_log then text else unit

val ilog: l:log_t{mac_log} -> Tot text
let ilog l = l

#set-options "--initial_fuel 1 --max_fuel 1"

val poly_cons: x:word -> xs:text -> r:elem ->
  Lemma (poly (Seq.cons x xs) r == (encode x +@ poly xs r) *@ r)
let poly_cons x xs r =
  let xxs = Seq.cons x xs in
  Seq.lemma_len_append (Seq.create 1 x) xs;
  Seq.lemma_eq_intro (Seq.tail xxs) xs

val poly_empty: t:text{Seq.length t == 0} -> r:elem ->
  Lemma (poly t r == 0)
let poly_empty t r = ()

#set-options "--z3rlimit 60 --initial_fuel 0 --max_fuel 0"

(**
   Update function:
   - takes a ghost log
   - takes a message block, appends '1' to it and formats it to bigint format
   - Updates acc = ((acc + block) * r) % p
   *)
val poly1305_update:
  current_log:log_t ->
  msg:wordB_16 ->
  acc:elemB{disjoint msg acc} ->
  r:elemB{disjoint msg r /\ disjoint acc r} ->
  Stack log_t
  (requires (fun h -> live h msg /\ norm h acc /\ norm h r
    /\ (mac_log ==> sel_elem h acc == poly (ilog current_log) (sel_elem h r)) ))
  (ensures (fun h0 updated_log h1 -> live h0 msg /\ norm h0 r
    /\ live h1 msg /\ norm h1 acc /\ norm h1 r
    /\ modifies_1 acc h0 h1
    /\ (mac_log ==>
       ilog updated_log == Seq.cons (sel_word h0 msg) (ilog current_log)
       /\ sel_elem h1 acc == poly (ilog updated_log) (sel_elem h0 r)) ))
let poly1305_update log msgB acc r =
  let h0 = ST.get () in
  push_frame();
  let block = create 0UL nlength in //TODO: pass buffer, don't create one
  toField_plus_2_128 block msgB;
  let h1 = ST.get () in
  eval_eq_lemma h0 h1 acc acc Parameters.norm_length;
  eval_eq_lemma h0 h1 r r Parameters.norm_length;
  add_and_multiply acc block r;
  let h2 = ST.get () in
  assert (sel_elem h2 acc ==
    (encode (sel_word h0 msgB) +@ sel_elem h0 acc) *@ sel_elem h0 r);
  let updated_log:log_t =
    if mac_log then
      let msg = read_word 16ul msgB in
      poly_cons (sel_word h0 msgB) (ilog log) (sel_elem h0 r);
      Seq.cons msg (ilog log)
    else ()
  in
  pop_frame();
  let h3 = ST.get () in
  eval_eq_lemma h2 h3 acc acc Parameters.norm_length;
  updated_log


(** Performs the last step if there is an incomplete block *)
val poly1305_last:
  current_log:log_t ->
  msg:wordB ->
  acc:elemB{disjoint msg acc} ->
  r:elemB{disjoint msg r /\ disjoint acc r} ->
  len:u32{w len == length msg /\ 0 < w len /\ w len < 16} ->
  Stack log_t
    (requires (fun h -> live h msg /\ norm h acc /\ norm h r
      /\ (mac_log ==> sel_elem h acc == poly (ilog current_log) (sel_elem h r)) ))
    (ensures (fun h0 updated_log h1 -> live h0 msg /\ norm h0 r
      /\ live h1 msg /\ norm h1 acc /\ norm h1 r
      /\ modifies_1 acc h0 h1
      /\ (mac_log ==>
         ilog updated_log == Seq.cons (sel_word h0 msg) (ilog current_log)
         /\ sel_elem h1 acc == poly (ilog updated_log) (sel_elem h0 r)) ))
let poly1305_last log msgB acc r len =
  let h0 = ST.get () in
  push_frame ();
  let block = create 0UL nlength in
  toField_plus len block msgB;
  let h1 = ST.get () in
  eval_eq_lemma h0 h1 acc acc Parameters.norm_length;
  eval_eq_lemma h0 h1 r r Parameters.norm_length;
  add_and_multiply acc block r;
  let h2 = ST.get () in
  assert (sel_elem h2 acc ==
    (encode (sel_word h0 msgB) +@ sel_elem h0 acc) *@ sel_elem h0 r);
  let updated_log:log_t =
    if mac_log then
      let msg = read_word len msgB in
      poly_cons (sel_word h0 msgB) (ilog log) (sel_elem h0 r);
      Seq.cons msg (ilog log)
    else ()
  in
  pop_frame ();
  let h3 = ST.get() in
  eval_eq_lemma h2 h3 acc acc Parameters.norm_length;
  updated_log


(* In Crypto.AEAD.Encoding *)
private let min (a:nat) (b:nat) : nat = if a <= b then a else b

val encode_bytes: txt:Seq.seq UInt8.t -> GTot text (decreases (Seq.length txt))
let rec encode_bytes txt =
  let l = Seq.length txt in
  if l = 0 then
    Seq.empty
  else
    let l0 = min l 16 in
    let w, txt = Seq.split txt l0 in
    Seq.snoc (encode_bytes txt) w // snoc, not cons!
(***)

#set-options "--initial_fuel 1 --max_fuel 1"

(** Auxiliary lemmas *)

val append_empty: #a:Type -> s1:Seq.seq a -> s2:Seq.seq a -> Lemma
  (requires (Seq.length s1 == 0))
  (ensures  (Seq.append s1 s2 == s2))
  [SMTPat (Seq.append s1 s2); SMTPat (Seq.length s1 == 0)]
let append_empty #a s1 s2 =
  Seq.lemma_eq_intro (Seq.append s1 s2) s2

val append_cons_snoc: #a:Type -> s1:Seq.seq a -> hd:a -> tl:Seq.seq a -> Lemma
  (Seq.append s1 (Seq.cons hd tl) ==
   Seq.append (Seq.snoc s1 hd) tl)
let append_cons_snoc #a s1 hd tl =
  Seq.lemma_eq_intro
    (Seq.append s1 (Seq.cons hd tl))
    (Seq.append (Seq.snoc s1 hd) tl)

val snoc_cons: #a:Type -> s:Seq.seq a -> x:a -> y:a -> Lemma
  (FStar.Seq (Seq.equal (snoc (cons x s) y) (cons x (snoc s y))))
let snoc_cons #a s x y = ()

val append_assoc: #a:Type -> s1:Seq.seq a -> s2:Seq.seq a -> s3:Seq.seq a -> Lemma
  (FStar.Seq (equal (append s1 (append s2 s3)) (append (append s1 s2) s3)))
let append_assoc #a s1 s2 s3 = ()

val append_as_seq_sub: h:mem -> n:UInt32.t -> m:UInt32.t -> msg:bytes{live h msg /\ w m <= w n /\ w n <= length msg} -> Lemma
  (append (as_seq h (Buffer.sub msg 0ul m))
          (as_seq h (Buffer.sub (Buffer.offset msg m) 0ul (U32 (n -^ m)))) ==
   as_seq h (Buffer.sub msg 0ul n))
let append_as_seq_sub h n m msg =
  Seq.lemma_eq_intro
    (append (as_seq h (Buffer.sub msg 0ul m))
            (as_seq h (Buffer.sub (Buffer.offset msg m) 0ul (U32 (n -^ m)))))
     (as_seq h (Buffer.sub msg 0ul n))

val append_as_seq: h:mem -> m:UInt32.t -> n:UInt32.t ->
  msg:bytes{live h msg /\ w m + w n == length msg} -> Lemma
  (Seq.equal
    (append (as_seq h (Buffer.sub msg 0ul m)) (as_seq h (Buffer.sub msg m n)))
    (as_seq h msg))
let append_as_seq h n m msg = ()

val encode_bytes_empty: txt:Seq.seq UInt8.t -> Lemma
    (requires Seq.length txt == 0)
    (ensures  encode_bytes txt == Seq.empty)
    [SMTPat (encode_bytes txt); SMTPat (Seq.length txt == 0)]
let encode_bytes_empty txt = ()

val snoc_encode_bytes: s:Seq.seq UInt8.t -> w:word_16 -> Lemma
  (Seq.equal (Seq.snoc (encode_bytes s) w) (encode_bytes (Seq.append w s)))
let snoc_encode_bytes s w =
  let txt0, txt1 = Seq.split (Seq.append w s) 16 in
  assert (Seq.equal w txt0 /\ Seq.equal s txt1)

val encode_bytes_append: len:U32.t -> s:Seq.seq UInt8.t -> w:word -> Lemma
  (requires (0 < Seq.length w /\ Seq.length s == U32.v len /\ U32.rem len 16ul == 0ul))
  (ensures  (Seq.equal (encode_bytes (Seq.append s w))
                      (Seq.cons w (encode_bytes s))))
  (decreases (Seq.length s))
let rec encode_bytes_append len s w =
  let open FStar.Seq in
  let txt = Seq.append s w in
  lemma_len_append s w;
  let l0 = min (length txt) 16 in
  let w', txt = split_eq txt l0 in
  if length s = 0 then
    begin
    assert (equal w w');
    encode_bytes_empty txt
    end
  else
    begin
    assert (l0 == 16);
    let w0, s' = split_eq s 16 in
    snoc_encode_bytes (append s' w) w0;
    append_assoc w0 s' w;
    snoc_cons (encode_bytes s') w w0;
    encode_bytes_append (U32(len -^ 16ul)) s' w
    end


#set-options "--z3rlimit 60 --initial_fuel 0 --max_fuel 0"

(* Loop over Poly1305_update; could go below MAC *)
val poly1305_loop: log:log_t -> msg:bytes -> acc:elemB{disjoint msg acc} ->
  r:elemB{disjoint msg r /\ disjoint acc r} -> ctr:u32{length msg >= 16 * w ctr} ->
  Stack log_t
  (requires (fun h -> live h msg /\ norm h acc /\ norm h r /\
      (mac_log ==>
        sel_elem h acc == poly (ilog log) (sel_elem h r)) ))
  (ensures (fun h0 updated_log h1 -> live h0 msg /\ norm h1 acc /\ norm h0 r /\
      modifies_1 acc h0 h1 /\
      (mac_log ==>
        ilog updated_log ==
        Seq.append (encode_bytes (as_seq h0 (sub msg 0ul (UInt32.mul 16ul ctr))))
                   (ilog log)
        /\ sel_elem h1 acc == poly (ilog updated_log) (sel_elem h0 r)) ))
    (decreases (w ctr))
let rec poly1305_loop log msg acc r ctr =
  let h0 = ST.get () in
  if U32.lte ctr 0ul then
    begin
    assert (Seq.length (as_seq h0 (Buffer.sub msg 0ul 0ul)) == 0);
    encode_bytes_empty (as_seq h0 (Buffer.sub msg 0ul 0ul));
    log
    end
  else
    begin
    let msg0:wordB_16 = sub msg 0ul 16ul in
    let log1 = poly1305_update log msg0 acc r in
    let h1 = ST.get () in
    let msg1 = offset msg 16ul in
    eval_eq_lemma h0 h1 r r norm_length;
    assert (live h1 msg1 /\ norm h1 acc /\ norm h1 r /\ modifies_1 acc h0 h1);
    let log2 = poly1305_loop log1 msg1 acc r (U32 (ctr -^ 1ul)) in
    if mac_log then
      begin
      assert (sel_elem h1 acc == poly (ilog log1) (sel_elem h0 r));
      assert (ilog log1 == Seq.cons (sel_word h0 msg0) (ilog log));
      let s = as_seq h0 (sub msg1 0ul (UInt32.mul 16ul (U32 (ctr -^ 1ul)))) in
      append_cons_snoc (encode_bytes s) (sel_word h0 msg0) (ilog log);
   //   assert (ilog log2 ==
   //     Seq.append (Seq.snoc (encode_bytes s)
   //                (sel_word h0 msg0)) (ilog log));
      snoc_encode_bytes
        (as_seq h0 (sub msg1 0ul (U32.mul 16ul (U32 (ctr -^ 1ul)))))
        (sel_word h0 msg0);
      append_as_seq_sub h0 (U32.mul 16ul ctr) 16ul msg
   //   assert (Seq.equal
   //     (Seq.snoc (encode_bytes s) (sel_word h0 msg0))
   //     (encode_bytes (as_seq h0 (Buffer.sub msg 0ul (UInt32.mul 16ul ctr)))))
      end;
    log2
   end


val div_aux: a:UInt32.t -> b:UInt32.t{w b <> 0} -> Lemma
  (requires True)
  (ensures FStar.UInt32(UInt.size (v a / v b) n))
  [SMTPat (FStar.UInt32(UInt.size (v a / v b) n))]
let div_aux a b = ()

#reset-options "--z3rlimit 200 --initial_fuel 0 --max_fuel 0 --max_ifuel 0 --initial_ifuel 0"

val poly1305_process:
    msg:bytes
  -> len:u32{w len == length msg}
  -> acc:elemB{disjoint msg acc}
  -> r:elemB{disjoint msg r /\ disjoint acc r}
  -> Stack unit
    (requires (fun h -> live h msg /\ norm h acc /\ norm h r /\ sel_elem h acc == 0))
    (ensures (fun h0 log h1 -> live h0 msg /\ norm h1 acc /\ norm h0 r /\
      modifies_1 acc h0 h1 /\
      (mac_log ==>
        sel_elem h1 acc == poly (encode_bytes (as_seq h0 msg)) (sel_elem h0 r))))
let poly1305_process msg len acc r =
  let h0 = ST.get () in
  let ctr, rem = U32.div len 16ul, U32.rem len 16ul in
  let log0:log_t = if mac_log then Seq.empty #word in
  if mac_log then poly_empty (ilog log0) (sel_elem h0 r);
  let log1 = poly1305_loop log0 msg acc r ctr in
  let h1 = ST.get () in
  assert (mac_log ==>
    Seq.equal (ilog log1)
      (encode_bytes (as_seq h0 (sub msg 0ul (UInt32.mul 16ul ctr))))
    /\ sel_elem h1 acc == poly (ilog log1) (sel_elem h0 r));
  if U32 (rem =^ 0ul) then
    Seq.lemma_eq_intro
      (as_seq h0 (sub msg 0ul (UInt32.mul 16ul ctr)))
      (as_seq h0 msg)
  else
    begin
    eval_eq_lemma h0 h1 r r norm_length;
    let last = sub msg (U32.mul 16ul ctr) rem in
    let log2 = poly1305_last log1 last acc r rem in
    let h2 = ST.get () in
    if mac_log then
      begin
        Seq.lemma_eq_intro
          (sel_word h1 last)
          (as_seq h0 (sub msg (U32.mul 16ul ctr) rem));
        encode_bytes_append (UInt32.mul 16ul ctr)
          (as_seq h0 (sub msg 0ul (UInt32.mul 16ul ctr)))
          (as_seq h0 (sub msg (U32.mul 16ul ctr) rem));
        append_as_seq h0 (UInt32.mul 16ul ctr) rem msg
      end
    end


open FStar.HyperStack
open FStar.Buffer

private let modifies_mac (#a1:Type) (#a2:Type) (#a3:Type) (#a4:Type)
  (b1:Buffer.buffer a1) (b2:Buffer.buffer a2) (b3:Buffer.buffer a3) (b4:Buffer.buffer a4)
  h0 h1 h2 h3 h4 h5 h6: Lemma
  (requires (  ~(contains h0 b1)
             /\ ~(contains h0 b2)
             /\ ~(contains h0 b3)
             /\ live h0 b4
             /\ fresh_frame h0 h1
             /\ modifies_0 h1 h2
             /\ live h2 b1 /\ live h2 b2 /\ live h2 b3
             /\ modifies_2 b1 b2 h2 h3
             /\ modifies_1 b3 h3 h4
             /\ modifies_2 b4 b3 h4 h5
             /\ popped h5 h6))
  (ensures  (modifies_1 b4 h0 h6))
  = lemma_reveal_modifies_0 h1 h2;
    lemma_reveal_modifies_2 b1 b2 h2 h3;
    lemma_reveal_modifies_1 b3 h3 h4;
    lemma_reveal_modifies_2 b4 b3 h4 h5;
    lemma_intro_modifies_1 b4 h0 h6


(** Computes the Poly1305 MAC on a buffer *)
val poly1305_mac:
  tag:wordB{length tag == 16} ->
  msg:bytes{disjoint tag msg} ->
  len:u32{w len == length msg} ->
  key:bytes{length key == 32 /\ disjoint msg key /\ disjoint tag key} ->
  Stack unit
    (requires (fun h -> live h msg /\ live h key /\ live h tag))
    (ensures (fun h0 _ h1 -> live h0 msg /\ live h0 key /\ live h1 tag
      /\ modifies_1 tag h0 h1
      /\ (let r = Spec.clamp (sel_word h0 (sub key 0ul 16ul)) in
         let s = sel_word h0 (sub key 16ul 16ul) in
         mac_log ==>
         Seq.equal
           (sel_word h1 tag)
           (mac_1305 (encode_bytes (as_seq h0 msg)) r s))))
let poly1305_mac tag msg len key =
  let h0 = ST.get () in
  push_frame();
  let h0' = ST.get () in

  (* Create buffers for the 2 parts of the key and the accumulator *)
  let tmp = create 0UL 10ul in
  let acc = sub tmp 0ul 5ul in
  let r   = sub tmp 5ul 5ul in
  let s   = create 0uy 16ul in
  let h0'' = ST.get () in

  (* Initialize the accumulator and the keys values *)
  poly1305_init r s key;
  let h1 = ST.get () in
  eval_null h1 acc norm_length;
  assert (sel_elem h1 acc == 0);

  (* Process the message bytes, updating the accumulator *)
  poly1305_process msg len acc r;
  let h2 = ST.get () in

  (* Finish *)
  poly1305_finish tag acc s;
  let h3 = ST.get () in
  assert (sel_word h3 tag == finish (sel_elem h2 acc) (sel_word h2 s));
  assert (mac_log ==>
    sel_word h3 tag ==
    mac_1305 (encode_bytes (as_seq h0 msg)) (sel_elem h1 r) (sel_word h1 s));

  pop_frame();
  let h4 = ST.get () in
  assert (Seq.equal (sel_word h4 tag) (sel_word h3 tag));
  modifies_mac r s acc tag h0 h0' h0'' h1 h2 h3 h4

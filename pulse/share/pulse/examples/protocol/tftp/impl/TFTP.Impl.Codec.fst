module TFTP.Impl.Codec

#lang-pulse

(**
  Verified Pulse implementation of the IETF TFTP (RFC 1350) codec leaves, proved
  against the hand-written wire format `TFTP.Wire` (the `tftp_message` union).

  Unlike the YMODEM codec, this leaf does NOT `friend` any generated module: the
  TFTP wire format is written by hand over `FStar.Seq`, so `tftp_serialize` /
  `tftp_parse` are ordinary transparent definitions and the correspondence proofs
  are direct.  The only real proof machinery is the big-endian byte<->U16
  correspondence for the 16-bit opcode / block-number / error-code fields.

  These are the executable leaves the driver loops (and the interop wrappers)
  link against; they take/return plain `array U8.t` buffers and extract to clean
  C.  DATA carries a variable-length (0..512) payload delimited by the UDP
  datagram, so `tftp_emit_data` / `tftp_recv_data` are parameterized by the
  payload length.
**)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module R = Pulse.Lib.Reference
module E = FStar.Endianness
module ML = FStar.Math.Lemmas
module UInt = FStar.UInt

open TFTP.Wire

(* ------------------------------------------------------------------------ *)
(* Big-endian byte <-> U16 correspondence.                                   *)
(* ------------------------------------------------------------------------ *)

(* The two big-endian bytes of a U16 (executable). *)
let u16_hi (x:U16.t) : U8.t = Cast.uint16_to_uint8 (U16.shift_right x 8ul)
let u16_lo (x:U16.t) : U8.t = Cast.uint16_to_uint8 x

(* Reassemble a U16 from its two big-endian bytes (executable). *)
let u16_of_bytes (hi lo:U8.t) : U16.t =
  U16.logor (U16.shift_left (Cast.uint8_to_uint16 hi) 8ul) (Cast.uint8_to_uint16 lo)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"

(* be_to_n of a 2-byte sequence, unfolded to a closed arithmetic form. *)
let lemma_be_to_n_2 (b:Seq.seq U8.t)
  : Lemma (requires Seq.length b == 2)
          (ensures E.be_to_n b == U8.v (Seq.index b 1) + 256 * U8.v (Seq.index b 0))
=
  E.reveal_be_to_n b;
  E.reveal_be_to_n (Seq.slice b 0 1);
  E.reveal_be_to_n (Seq.slice (Seq.slice b 0 1) 0 0);
  assert (Seq.index (Seq.slice b 0 1) 0 == Seq.index b 0)

(* enc16 encodes a U16 as exactly its two big-endian bytes. *)
let lemma_enc16_bytes (x:U16.t)
  : Lemma (enc16 x == Seq.append (Seq.create 1 (u16_hi x)) (Seq.create 1 (u16_lo x)))
=
  let hi = u16_hi x in
  let lo = u16_lo x in
  let b = Seq.append (Seq.create 1 hi) (Seq.create 1 lo) in
  assert_norm (pow2 8 == 256);
  SP.append_slices (Seq.create 1 hi) (Seq.create 1 lo);
  Seq.lemma_index_app2 (Seq.create 1 hi) (Seq.create 1 lo) 1;
  lemma_be_to_n_2 b;
  (* U8.v hi == U16.v x / 256 (shift_right SMTPat + the < 65536 bound),
     U8.v lo == U16.v x % 256 (uint16_to_uint8 spec) *)
  ML.euclidean_division_definition (U16.v x) 256;
  E.n_to_be_be_to_n 2 (enc16 x);
  E.be_to_n_inj b (enc16 x)

(* u16_of_bytes inverts the two big-endian bytes: it agrees with dec16. *)
let lemma_u16_of_bytes (hi lo:U8.t)
  : Lemma (u16_of_bytes hi lo == dec16 (Seq.append (Seq.create 1 hi) (Seq.create 1 lo)))
=
  let b = Seq.append (Seq.create 1 hi) (Seq.create 1 lo) in
  assert_norm (pow2 8 == 256);
  SP.append_slices (Seq.create 1 hi) (Seq.create 1 lo);
  Seq.lemma_index_app2 (Seq.create 1 hi) (Seq.create 1 lo) 1;
  lemma_be_to_n_2 b;
  (* v (shift_left (u8->u16 hi) 8) == (U8.v hi * 256) % pow2 16 == U8.v hi * 256 *)
  UInt.shift_left_value_lemma #16 (U8.v hi) 8;
  ML.small_mod (U8.v hi * 256) (pow2 16);
  (* logor of the shifted hi (low 8 bits zero) and lo (< 256) is addition *)
  UInt.logor_disjoint #16 (U8.v hi * 256) (U8.v lo) 8;
  E.lemma_be_to_n_is_bounded b

#pop-options

(* ------------------------------------------------------------------------ *)
(* Pure serialize/parse correspondence (existential packaging).              *)
(* ------------------------------------------------------------------------ *)

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"

(* A concrete 4+len byte buffer that carries the DATA layout equals the
   serialization of the corresponding Msg_data. *)
let emit_data_serialize (blk:U16.t) (d:data_payload) (s:Seq.seq U8.t)
  : Lemma
    (requires
       Seq.length s == 4 + Seq.length (d <: Seq.seq U8.t) /\
       Seq.index s 0 == u16_hi op_data /\
       Seq.index s 1 == u16_lo op_data /\
       Seq.index s 2 == u16_hi blk /\
       Seq.index s 3 == u16_lo blk /\
       (forall (j:nat). j < Seq.length (d <: Seq.seq U8.t) ==>
          Seq.index s (4 + j) == Seq.index (d <: Seq.seq U8.t) j))
    (ensures s == tftp_serialize (Msg_data blk d))
=
  lemma_enc16_bytes op_data;
  lemma_enc16_bytes blk;
  Seq.lemma_eq_intro s (tftp_serialize (Msg_data blk d))

let emit_data_exists (blk:U16.t) (d s:Seq.seq U8.t)
  : Lemma
    (requires
       Seq.length d <= 512 /\
       Seq.length s == 4 + Seq.length d /\
       Seq.index s 0 == u16_hi op_data /\
       Seq.index s 1 == u16_lo op_data /\
       Seq.index s 2 == u16_hi blk /\
       Seq.index s 3 == u16_lo blk /\
       (forall (j:nat). j < Seq.length d ==> Seq.index s (4 + j) == Seq.index d j))
    (ensures
       (exists (pl:data_payload).
          (pl <: Seq.seq U8.t) == d /\ s == tftp_serialize (Msg_data blk pl)))
=
  let pl : data_payload = d in
  emit_data_serialize blk pl s;
  introduce exists (pl':data_payload).
     (pl' <: Seq.seq U8.t) == d /\ s == tftp_serialize (Msg_data blk pl')
  with pl and ()

(* An ACK layout equals the serialization of the corresponding Msg_ack. *)
let emit_ack_serialize (blk:U16.t) (s:Seq.seq U8.t)
  : Lemma
    (requires
       Seq.length s == 4 /\
       Seq.index s 0 == u16_hi op_ack /\
       Seq.index s 1 == u16_lo op_ack /\
       Seq.index s 2 == u16_hi blk /\
       Seq.index s 3 == u16_lo blk)
    (ensures s == tftp_serialize (Msg_ack blk))
=
  lemma_enc16_bytes op_ack;
  lemma_enc16_bytes blk;
  Seq.lemma_eq_intro s (tftp_serialize (Msg_ack blk))

(* enc16 inverts dec16 on any 2-byte sequence. *)
let lemma_dec16_enc16 (b:Seq.seq U8.t)
  : Lemma (requires Seq.length b == 2) (ensures enc16 (dec16 b) == b)
=
  E.lemma_be_to_n_is_bounded b;
  E.n_to_be_be_to_n 2 b

(* An RRQ layout equals the serialization of the corresponding Msg_rrq. *)
let emit_rrq_serialize (fn0 md0 s:Seq.seq U8.t)
  : Lemma
    (requires
       zero_free fn0 /\ zero_free md0 /\
       Seq.length s == 2 + Seq.length fn0 + 1 + Seq.length md0 + 1 /\
       Seq.index s 0 == u16_hi op_rrq /\ Seq.index s 1 == u16_lo op_rrq /\
       (forall (j:nat). j < Seq.length fn0 ==> Seq.index s (2 + j) == Seq.index fn0 j) /\
       Seq.index s (2 + Seq.length fn0) == 0uy /\
       (forall (j:nat). j < Seq.length md0 ==>
          Seq.index s (2 + Seq.length fn0 + 1 + j) == Seq.index md0 j) /\
       Seq.index s (2 + Seq.length fn0 + 1 + Seq.length md0) == 0uy)
    (ensures
       (exists (fname:cstring) (mname:cstring).
          (fname <: Seq.seq U8.t) == fn0 /\ (mname <: Seq.seq U8.t) == md0 /\
          s == tftp_serialize (Msg_rrq fname mname)))
=
  let fname : cstring = fn0 in
  let mname : cstring = md0 in
  lemma_enc16_bytes op_rrq;
  Seq.lemma_eq_intro s (tftp_serialize (Msg_rrq fname mname));
  introduce exists (fname':cstring) (mname':cstring).
     (fname' <: Seq.seq U8.t) == fn0 /\ (mname' <: Seq.seq U8.t) == md0 /\
     s == tftp_serialize (Msg_rrq fname' mname')
  with fname mname
  and ()

(* An ERROR layout equals the serialization of the corresponding Msg_error. *)
let emit_error_serialize (code:U16.t) (em0 s:Seq.seq U8.t)
  : Lemma
    (requires
       zero_free em0 /\
       Seq.length s == 4 + Seq.length em0 + 1 /\
       Seq.index s 0 == u16_hi op_error /\ Seq.index s 1 == u16_lo op_error /\
       Seq.index s 2 == u16_hi code /\ Seq.index s 3 == u16_lo code /\
       (forall (j:nat). j < Seq.length em0 ==> Seq.index s (4 + j) == Seq.index em0 j) /\
       Seq.index s (4 + Seq.length em0) == 0uy)
    (ensures
       (exists (em:cstring).
          (em <: Seq.seq U8.t) == em0 /\ s == tftp_serialize (Msg_error code em)))
=
  let em : cstring = em0 in
  lemma_enc16_bytes op_error;
  lemma_enc16_bytes code;
  Seq.lemma_eq_intro s (tftp_serialize (Msg_error code em));
  introduce exists (em':cstring).
     (em' <: Seq.seq U8.t) == em0 /\ s == tftp_serialize (Msg_error code em')
  with em
  and ()

(* A concrete 4+len byte DATA buffer parses (via tftp_parse) to the Msg_data
   whose block number is `blk` and whose payload is the buffer tail. *)
let recv_data_exists (i o':Seq.seq U8.t) (blk:U16.t)
  : Lemma
    (requires
       Seq.length i == 4 + Seq.length o' /\ Seq.length o' <= 512 /\
       Seq.index i 0 == u16_hi op_data /\
       Seq.index i 1 == u16_lo op_data /\
       blk == u16_of_bytes (Seq.index i 2) (Seq.index i 3) /\
       (forall (j:nat). j < Seq.length o' ==> Seq.index o' j == Seq.index i (4 + j)))
    (ensures
       (exists (pl:data_payload) (rest:Seq.seq U8.t).
          tftp_parse i == Some (Msg_data blk pl, rest) /\ (pl <: Seq.seq U8.t) == o'))
=
  let pl : data_payload = o' in
  lemma_enc16_bytes op_data;
  lemma_u16_of_bytes (Seq.index i 2) (Seq.index i 3);
  lemma_dec16_enc16 (Seq.append (Seq.create 1 (Seq.index i 2)) (Seq.create 1 (Seq.index i 3)));
  Seq.lemma_eq_intro (tftp_serialize (Msg_data blk pl)) i;
  lemma_tftp_parse_serialize_exact (Msg_data blk pl);
  eliminate exists (parsed:tftp_message).
     tftp_parse (tftp_serialize (Msg_data blk pl)) == Some (parsed, Seq.empty) /\ parsed == Msg_data blk pl
  with
  ( introduce exists (pl2:data_payload) (rest:Seq.seq U8.t).
       tftp_parse i == Some (Msg_data blk pl2, rest) /\ (pl2 <: Seq.seq U8.t) == o'
    with pl Seq.empty
    and () )

(* A concrete 4-byte ACK buffer parses to Msg_ack of the encoded block. *)
let recv_ack_exists (i:Seq.seq U8.t) (blk:U16.t)
  : Lemma
    (requires
       Seq.length i == 4 /\
       Seq.index i 0 == u16_hi op_ack /\
       Seq.index i 1 == u16_lo op_ack /\
       blk == u16_of_bytes (Seq.index i 2) (Seq.index i 3))
    (ensures (exists (rest:Seq.seq U8.t). tftp_parse i == Some (Msg_ack blk, rest)))
=
  lemma_enc16_bytes op_ack;
  lemma_u16_of_bytes (Seq.index i 2) (Seq.index i 3);
  lemma_dec16_enc16 (Seq.append (Seq.create 1 (Seq.index i 2)) (Seq.create 1 (Seq.index i 3)));
  Seq.lemma_eq_intro (tftp_serialize (Msg_ack blk)) i;
  lemma_tftp_parse_serialize_exact (Msg_ack blk);
  eliminate exists (parsed:tftp_message).
     tftp_parse (tftp_serialize (Msg_ack blk)) == Some (parsed, Seq.empty) /\ parsed == Msg_ack blk
  with
  ( introduce exists (rest:Seq.seq U8.t). tftp_parse i == Some (Msg_ack blk, rest)
    with Seq.empty
    and () )

(* The 2-byte opcode read by `u16_of_bytes` is exactly the opcode the parser
   discriminates on (`dec16 (slice input 0 2)`). *)
let peek_opcode_correct (i:Seq.seq U8.t)
  : Lemma (requires Seq.length i >= 2)
          (ensures u16_of_bytes (Seq.index i 0) (Seq.index i 1) == dec16 (Seq.slice i 0 2))
=
  lemma_u16_of_bytes (Seq.index i 0) (Seq.index i 1);
  Seq.lemma_eq_intro (Seq.slice i 0 2)
    (Seq.append (Seq.create 1 (Seq.index i 0)) (Seq.create 1 (Seq.index i 1)))

#pop-options

(* ------------------------------------------------------------------------ *)
(* The verified leaves.                                                      *)
(* ------------------------------------------------------------------------ *)


open FStar.SizeT { (+), (-), ( * ), (/), (%), (<), (<=), (>), (>=) }
(* Build a TFTP DATA packet  03 | blk(2) | payload(len)  from a `len`-byte file
   chunk; `out` (length 4+len) receives the whole packet, proved equal to
   `tftp_serialize (Msg_data blk payload)`. *)
#push-options "--z3rlimit 30 --fuel 2 --ifuel 2"
fn tftp_emit_data
  (blk: U16.t)
  (data: array U8.t)
  (data_len: SZ.t)
  (out: array U8.t)
  requires
    pts_to data 'd **
    pts_to out 'o **
    pure (Seq.length 'd == SZ.v data_len /\ SZ.v data_len <= 512 /\
          Seq.length 'o == 4 + SZ.v data_len)
  ensures
    pts_to data 'd **
    (exists* (o':Seq.seq U8.t).
       pts_to out o' **
       pure (Seq.length o' == 4 + SZ.v data_len /\
             (exists (pl:data_payload).
                (pl <: Seq.seq U8.t) == 'd /\
                o' == tftp_serialize (Msg_data blk pl))))
{
  out.(0sz) <- u16_hi op_data;
  out.(1sz) <- u16_lo op_data;
  out.(2sz) <- u16_hi blk;
  out.(3sz) <- u16_lo blk;
  let mut i = 0sz;
  while (!i < data_len)
  invariant exists* (vi:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to i vi **
    pts_to data 'd **
    pts_to out sv **
    pure (
      SZ.v vi <= SZ.v data_len /\
      Seq.length 'd == SZ.v data_len /\
      Seq.length sv == 4 + SZ.v data_len /\
      Seq.index sv 0 == u16_hi op_data /\
      Seq.index sv 1 == u16_lo op_data /\
      Seq.index sv 2 == u16_hi blk /\
      Seq.index sv 3 == u16_lo blk /\
      (forall (j:nat). j < SZ.v vi ==> Seq.index sv (4 + j) == Seq.index 'd j))
  decreases (Prims.op_Minus (SZ.v data_len) (SZ.v (!i)))
  {
    let vi = !i;
    let dv = data.(vi);
    out.(4sz + vi) <- dv;
    i := vi + 1sz;
  };
  with sf. assert (pts_to out sf);
  emit_data_exists blk 'd sf;
  ()
}
#pop-options

(* Build a TFTP ACK packet  04 | blk(2), proved equal to the serialization of
   `Msg_ack blk`. *)
#push-options "--z3rlimit 20 --fuel 2 --ifuel 2"
fn tftp_emit_ack
  (blk: U16.t)
  (out: array U8.t)
  requires
    pts_to out 'o **
    pure (Seq.length 'o == 4)
  ensures
    (exists* (o':Seq.seq U8.t).
       pts_to out o' **
       pure (Seq.length o' == 4 /\ o' == tftp_serialize (Msg_ack blk)))
{
  out.(0sz) <- u16_hi op_ack;
  out.(1sz) <- u16_lo op_ack;
  out.(2sz) <- u16_hi blk;
  out.(3sz) <- u16_lo blk;
  with sf. assert (pts_to out sf);
  emit_ack_serialize blk sf;
  ()
}
#pop-options

(* Parse a TFTP DATA packet (opcode 3): copy the payload  inp[4 .. inp_len)  into
   `out_payload` and return the block number.  The payload length is the datagram
   length minus 4 (the datagram boundary supplies it). *)
#push-options "--z3rlimit 30 --fuel 2 --ifuel 2"
fn tftp_recv_data
  (inp: array U8.t)
  (inp_len: SZ.t)
  (out_payload: array U8.t)
  requires
    pts_to inp 'i **
    pts_to out_payload 'o **
    pure (Seq.length 'i == SZ.v inp_len /\ SZ.v inp_len >= 4 /\ SZ.v inp_len <= 516 /\
          SZ.v inp_len == Seq.length 'o + 4 /\
          Seq.index 'i 0 == u16_hi op_data /\ Seq.index 'i 1 == u16_lo op_data)
  returns blk: U16.t
  ensures
    pts_to inp 'i **
    (exists* (o':Seq.seq U8.t).
       pts_to out_payload o' **
       pure (SZ.v inp_len == Seq.length o' + 4 /\
             (exists (pl:data_payload) (rest:Seq.seq U8.t).
                tftp_parse 'i == Some (Msg_data blk pl, rest) /\ (pl <: Seq.seq U8.t) == o')))
{
  let plen = inp_len - 4sz;
  let mut i = 0sz;
  while (!i < plen)
  invariant exists* (vi:SZ.t) (ov:Seq.seq U8.t).
    R.pts_to i vi **
    pts_to inp 'i **
    pts_to out_payload ov **
    pure (
      SZ.v vi <= SZ.v plen /\
      Seq.length 'i == SZ.v inp_len /\
      SZ.v inp_len == Seq.length ov + 4 /\
      (forall (j:nat). j < SZ.v vi ==> Seq.index ov j == Seq.index 'i (4 + j)))
  decreases (Prims.op_Minus (SZ.v plen) (SZ.v (!i)))
  {
    let vi = !i;
    let dv = inp.(4sz + vi);
    out_payload.(vi) <- dv;
    i := vi + 1sz;
  };
  let b2 = inp.(2sz);
  let b3 = inp.(3sz);
  let blk = u16_of_bytes b2 b3;
  with ov. assert (pts_to out_payload ov);
  recv_data_exists 'i ov blk;
  blk
}
#pop-options

(* Parse a TFTP ACK packet (opcode 4): return the acknowledged block number. *)
#push-options "--z3rlimit 20 --fuel 2 --ifuel 2"
fn tftp_recv_ack
  (inp: array U8.t)
  requires
    pts_to inp 'i **
    pure (Seq.length 'i == 4 /\
          Seq.index 'i 0 == u16_hi op_ack /\ Seq.index 'i 1 == u16_lo op_ack)
  returns blk: U16.t
  ensures
    pts_to inp 'i **
    pure (exists (rest:Seq.seq U8.t). tftp_parse 'i == Some (Msg_ack blk, rest))
{
  let b2 = inp.(2sz);
  let b3 = inp.(3sz);
  let blk = u16_of_bytes b2 b3;
  recv_ack_exists 'i blk;
  blk
}
#pop-options

(* Build a TFTP RRQ packet  01 | filename | 00 | mode | 00.  The caller supplies
   NUL-free filename/mode buffers; `out` (length 2+|fn|+1+|md|+1) receives the
   whole packet, proved equal to `tftp_serialize (Msg_rrq filename mode)`. *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
fn tftp_emit_rrq
  (filename: array U8.t)
  (fn_len: SZ.t)
  (mode: array U8.t)
  (mode_len: SZ.t)
  (out: array U8.t)
  requires
    pts_to filename 'fnb **
    pts_to mode 'mdb **
    pts_to out 'o **
    pure (Seq.length 'fnb == SZ.v fn_len /\ Seq.length 'mdb == SZ.v mode_len /\
          zero_free 'fnb /\ zero_free 'mdb /\
          (2 <: nat) + SZ.v fn_len + 1 + SZ.v mode_len + 1 < (pow2 16 <: nat) /\
          Seq.length 'o == (2 <: nat) + SZ.v fn_len + 1 + SZ.v mode_len + 1)
  ensures
    pts_to filename 'fnb **
    pts_to mode 'mdb **
    (exists* (o':Seq.seq U8.t).
       pts_to out o' **
       pure (Seq.length o' == (2 <: nat) + SZ.v fn_len + 1 + SZ.v mode_len + 1 /\
             (exists (fname:cstring) (mname:cstring).
                (fname <: Seq.seq U8.t) == 'fnb /\ (mname <: Seq.seq U8.t) == 'mdb /\
                o' == tftp_serialize (Msg_rrq fname mname))))
{
  out.(0sz) <- u16_hi op_rrq;
  out.(1sz) <- u16_lo op_rrq;
  let mut i = 0sz;
  while (!i < fn_len)
  invariant exists* (vi:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to i vi **
    pts_to filename 'fnb **
    pts_to out sv **
    pure (
      SZ.v vi <= SZ.v fn_len /\
      Seq.length 'fnb == SZ.v fn_len /\
      (2 <: nat) + SZ.v fn_len + 1 + SZ.v mode_len + 1 < (pow2 16 <: nat) /\
      Seq.length sv == (2 <: nat) + SZ.v fn_len + 1 + SZ.v mode_len + 1 /\
      Seq.index sv 0 == u16_hi op_rrq /\
      Seq.index sv 1 == u16_lo op_rrq /\
      (forall (j:nat). j < SZ.v vi ==> Seq.index sv (2 + j) == Seq.index 'fnb j))
  decreases (Prims.op_Minus (SZ.v fn_len) (SZ.v (!i)))
  {
    let vi = !i;
    let dv = filename.(vi);
    out.(2sz + vi) <- dv;
    i := vi + 1sz;
  };
  out.(2sz + fn_len) <- 0uy;
  let mut k = 0sz;
  while (!k < mode_len)
  invariant exists* (vk:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to k vk **
    pts_to mode 'mdb **
    pts_to out sv **
    pure (
      SZ.v vk <= SZ.v mode_len /\
      Seq.length 'mdb == SZ.v mode_len /\
      (2 <: nat) + SZ.v fn_len + 1 + SZ.v mode_len + 1 < (pow2 16 <: nat) /\
      Seq.length sv == (2 <: nat) + SZ.v fn_len + 1 + SZ.v mode_len + 1 /\
      Seq.index sv 0 == u16_hi op_rrq /\
      Seq.index sv 1 == u16_lo op_rrq /\
      (forall (j:nat). j < SZ.v fn_len ==> Seq.index sv (2 + j) == Seq.index 'fnb j) /\
      Seq.index sv ((2 <: nat) + SZ.v fn_len) == 0uy /\
      (forall (j:nat). j < SZ.v vk ==>
         Seq.index sv ((2 <: nat) + SZ.v fn_len + 1 + j) == Seq.index 'mdb j))
  decreases (Prims.op_Minus (SZ.v mode_len) (SZ.v (!k)))
  {
    let vk = !k;
    let dv = mode.(vk);
    out.(2sz + fn_len + 1sz + vk) <- dv;
    k := vk + 1sz;
  };
  out.(2sz + fn_len + 1sz + mode_len) <- 0uy;
  with sf. assert (pts_to out sf);
  emit_rrq_serialize 'fnb 'mdb sf;
  ()
}
#pop-options

(* Build a TFTP ERROR packet  05 | code(2) | msg | 00, proved equal to
   `tftp_serialize (Msg_error code msg)`. *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
fn tftp_emit_error
  (code: U16.t)
  (msg: array U8.t)
  (msg_len: SZ.t)
  (out: array U8.t)
  requires
    pts_to msg 'em **
    pts_to out 'o **
    pure (Seq.length 'em == SZ.v msg_len /\ zero_free 'em /\
          4 + SZ.v msg_len + 1 < (pow2 16 <: nat) /\
          Seq.length 'o == 4 + SZ.v msg_len + 1)
  ensures
    pts_to msg 'em **
    (exists* (o':Seq.seq U8.t).
       pts_to out o' **
       pure (Seq.length o' == 4 + SZ.v msg_len + 1 /\
             (exists (emsg:cstring).
                (emsg <: Seq.seq U8.t) == 'em /\
                o' == tftp_serialize (Msg_error code emsg))))
{
  out.(0sz) <- u16_hi op_error;
  out.(1sz) <- u16_lo op_error;
  out.(2sz) <- u16_hi code;
  out.(3sz) <- u16_lo code;
  let mut i = 0sz;
  while (!i < msg_len)
  invariant exists* (vi:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to i vi **
    pts_to msg 'em **
    pts_to out sv **
    pure (
      SZ.v vi <= SZ.v msg_len /\
      Seq.length 'em == SZ.v msg_len /\
      4 + SZ.v msg_len + 1 < (pow2 16 <: nat) /\
      Seq.length sv == 4 + SZ.v msg_len + 1 /\
      Seq.index sv 0 == u16_hi op_error /\
      Seq.index sv 1 == u16_lo op_error /\
      Seq.index sv 2 == u16_hi code /\
      Seq.index sv 3 == u16_lo code /\
      (forall (j:nat). j < SZ.v vi ==> Seq.index sv (4 + j) == Seq.index 'em j))
  decreases (Prims.op_Minus (SZ.v msg_len) (SZ.v (!i)))
  {
    let vi = !i;
    let dv = msg.(vi);
    out.(4sz + vi) <- dv;
    i := vi + 1sz;
  };
  out.(4sz + msg_len) <- 0uy;
  with sf. assert (pts_to out sf);
  emit_error_serialize code 'em sf;
  ()
}
#pop-options

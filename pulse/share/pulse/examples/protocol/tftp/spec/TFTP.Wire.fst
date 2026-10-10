module TFTP.Wire

(**
  Instantiation of the `Pulse.Lib.Protocol.WireFormat.wire_format` type class for the IETF
  TFTP (RFC 1350) wire messages — the five packet types RRQ / WRQ / DATA / ACK /
  ERROR, as a single opcode-discriminated union `tftp_message`.

  ── Why this is written and proved BY HAND (not QuackyDucky) ─────────────────
  The TFTP wire format exceeds the expressive power of EverParse/QuackyDucky:

    1. RRQ/WRQ (filename, mode) and ERROR (message) carry *NUL-terminated,
       variable-length strings*, a construct the QuackyDucky `.rfc` DSL cannot
       express (it has only fixed-size arrays and length-prefixed vldata).

    2. The DATA payload has *no length field*: its length is the enclosing UDP
       datagram's length.  So DATA is *datagram-delimited*, not
       content-self-delimiting.

  This module therefore defines `tftp_serialize` / `tftp_parse` directly over
  `FStar.Seq` (big-endian 16-bit fields via `FStar.Endianness`) and discharges
  the `Pulse.Lib.Protocol.WireFormat` round-trip law `wf_parse_serialize_exact` by hand.

  ── The datagram boundary (see the plan §3.1) ───────────────────────────────
  Because DATA takes "all remaining bytes" as its payload,
  `tftp_parse (serialize (Msg_data blk d) ++ rest)` would parse `Msg_data blk
  (d ++ rest)`, NOT `(Msg_data blk d, rest)`.  Hence DATA is *not* a strong
  (prefix) parser and we deliberately do NOT instantiate the OPTIONAL
  `Pulse.Lib.Protocol.WireFormat.wire_format_stream_laws`.  This is sound: the driver
  (`Pulse.Lib.Protocol.Implementation.network_process_correct`) only needs
  per-datagram `wf_parse` — the loop hands it exactly one datagram at a time
  (one `recvfrom`), so buffer-end == message-end == empty residual, which is
  exactly what `wf_parse_serialize_exact` establishes.  RRQ/WRQ/ACK/ERROR *are*
  self-delimiting (NUL-terminated or fixed 4 bytes); only DATA relies on the
  boundary.
**)

module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module E = FStar.Endianness
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module TCP = Pulse.Lib.TCP
module WF = Pulse.Lib.Protocol.WireFormat

(* ───────────────────────────────────────────────────────────────────────────
   NUL-free byte strings (the TFTP "netascii" fields: filename, mode, errmsg).

   A field is terminated on the wire by a 0x00 byte, so a well-formed field
   contains no embedded 0x00.  `zero_free` is a total boolean predicate (usable
   in refinements) recognising such strings.
   ─────────────────────────────────────────────────────────────────────────── *)
let rec zero_free (b:TCP.bytes) : Tot bool (decreases Seq.length b) =
  if Seq.length b = 0 then true
  else Seq.index b 0 <> 0uy && zero_free (Seq.slice b 1 (Seq.length b))

(* A NUL-terminated-string payload: the bytes strictly before the terminator. *)
type cstring = s:TCP.bytes { zero_free s }

(* A DATA payload is at most 512 bytes (stock TFTP block size). *)
type data_payload = b:TCP.bytes { Seq.length b <= 512 }

(* ───────────────────────────────────────────────────────────────────────────
   The TFTP message union (RFC 1350 §5).  All 16-bit fields are big-endian.

     RRQ    | 01 | Filename | 00 | Mode | 00 |
     WRQ    | 02 | Filename | 00 | Mode | 00 |
     DATA   | 03 | Block(2) | Data(0..512) |
     ACK    | 04 | Block(2) |
     ERROR  | 05 | ErrorCode(2) | ErrMsg | 00 |
   ─────────────────────────────────────────────────────────────────────────── *)
noeq
type tftp_message =
  | Msg_rrq   : filename:cstring -> mode:cstring -> tftp_message
  | Msg_wrq   : filename:cstring -> mode:cstring -> tftp_message
  | Msg_data  : block:U16.t -> payload:data_payload -> tftp_message
  | Msg_ack   : block:U16.t -> tftp_message
  | Msg_error : code:U16.t -> msg:cstring -> tftp_message

(* Opcodes as 16-bit values (bounds come for free from the U16 type). *)
inline_for_extraction let op_rrq   : U16.t = 1us
inline_for_extraction let op_wrq   : U16.t = 2us
inline_for_extraction let op_data  : U16.t = 3us
inline_for_extraction let op_ack   : U16.t = 4us
inline_for_extraction let op_error : U16.t = 5us

(* Encode a 16-bit field big-endian; `n_to_be`'s return type already gives the
   inverse fact `U16.v x == be_to_n (enc16 x)`. *)
let enc16 (x:U16.t) : TCP.bytes = E.n_to_be 2 (U16.v x)

(* Decode a 2-byte big-endian field.  The 2-byte length bounds `be_to_n` below
   `pow2 16`, so the `U16.uint_to_t` is well-typed. *)
let dec16 (b:TCP.bytes{Seq.length b == 2}) : U16.t =
  E.lemma_be_to_n_is_bounded b;
  U16.uint_to_t (E.be_to_n b)

(* ───────────────────────────────────────────────────────────────────────────
   Serialization.
   ─────────────────────────────────────────────────────────────────────────── *)
let tftp_serialize (m:tftp_message) : GTot TCP.bytes =
  match m with
  | Msg_rrq fn md ->
    Seq.append (enc16 op_rrq)
      (Seq.append fn (Seq.cons 0uy (Seq.append md (Seq.cons 0uy Seq.empty))))
  | Msg_wrq fn md ->
    Seq.append (enc16 op_wrq)
      (Seq.append fn (Seq.cons 0uy (Seq.append md (Seq.cons 0uy Seq.empty))))
  | Msg_data blk pl ->
    Seq.append (enc16 op_data) (Seq.append (enc16 blk) pl)
  | Msg_ack blk ->
    Seq.append (enc16 op_ack) (enc16 blk)
  | Msg_error code em ->
    Seq.append (enc16 op_error)
      (Seq.append (enc16 code) (Seq.append em (Seq.cons 0uy Seq.empty)))

(* ───────────────────────────────────────────────────────────────────────────
   NUL-terminated field scan: split `b` at the first 0x00 into
   (bytes-before, bytes-after), or None if there is no terminator.
   ─────────────────────────────────────────────────────────────────────────── *)
let rec split_cstr (b:TCP.bytes)
  : GTot (option (TCP.bytes & TCP.bytes)) (decreases Seq.length b) =
  if Seq.length b = 0 then None
  else if Seq.index b 0 = 0uy then Some (Seq.empty, Seq.slice b 1 (Seq.length b))
  else
    (match split_cstr (Seq.slice b 1 (Seq.length b)) with
     | None -> None
     | Some (pre, post) -> Some (Seq.cons (Seq.index b 0) pre, post))

(* ───────────────────────────────────────────────────────────────────────────
   Parsing (the `Pulse.Lib.Protocol.WireFormat` convention: return the message plus the
   unconsumed residual).  DATA takes all remaining bytes as its payload and
   leaves an empty residual (the datagram boundary supplies the length).
   ─────────────────────────────────────────────────────────────────────────── *)
let tftp_parse (input:TCP.bytes) : GTot (WF.parse_result tftp_message) =
  if Seq.length input < 2 then None
  else
    let op = E.be_to_n (Seq.slice input 0 2) in
    let body = Seq.slice input 2 (Seq.length input) in
    if op = U16.v op_rrq || op = U16.v op_wrq then
      (match split_cstr body with
       | None -> None
       | Some (fn, rest1) ->
         if not (zero_free fn) then None
         else
           (match split_cstr rest1 with
            | None -> None
            | Some (md, rest2) ->
              if not (zero_free md) then None
              else Some ((if op = U16.v op_rrq then Msg_rrq fn md else Msg_wrq fn md), rest2)))
    else if op = U16.v op_data then
      (if Seq.length body < 2 then None
       else
         let blk = dec16 (Seq.slice body 0 2) in
         let pl = Seq.slice body 2 (Seq.length body) in
         if Seq.length pl <= 512 then Some (Msg_data blk pl, Seq.empty) else None)
    else if op = U16.v op_ack then
      (if Seq.length body < 2 then None
       else
         let blk = dec16 (Seq.slice body 0 2) in
         Some (Msg_ack blk, Seq.slice body 2 (Seq.length body)))
    else if op = U16.v op_error then
      (if Seq.length body < 2 then None
       else
         let code = dec16 (Seq.slice body 0 2) in
         let rest0 = Seq.slice body 2 (Seq.length body) in
         (match split_cstr rest0 with
          | None -> None
          | Some (em, rest1) ->
            if not (zero_free em) then None
            else Some (Msg_error code em, rest1)))
    else None

(* ───────────────────────────────────────────────────────────────────────────
   Key lemma: `split_cstr` inverts the "field ++ 0x00 ++ rest" layout when the
   field is NUL-free.
   ─────────────────────────────────────────────────────────────────────────── *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec split_cstr_append (s rest:TCP.bytes)
  : Lemma
      (requires zero_free s)
      (ensures split_cstr (Seq.append s (Seq.cons 0uy rest)) == Some (s, rest))
      (decreases Seq.length s)
=
  let tr = Seq.cons 0uy rest in
  let full = Seq.append s tr in
  if Seq.length s = 0 then begin
    Seq.append_empty_l tr;
    Seq.lemma_eq_elim full tr;
    SP.head_cons 0uy rest;   (* Seq.head (cons 0uy rest) == 0uy, and head == index 0 *)
    SP.lemma_tl 0uy rest;    (* Seq.tail (cons 0uy rest) == rest *)
    Seq.lemma_eq_elim s Seq.empty;
    assert (Seq.index full 0 == 0uy);
    assert (Seq.slice full 1 (Seq.length full) == rest)
  end
  else begin
    SP.lemma_slice_first_in_append s tr 1;  (* slice full 1 len == append (tail s) tr *)
    Seq.lemma_index_app1 s tr 0;            (* index full 0 == index s 0 *)
    assert (Seq.index s 0 <> 0uy);
    assert (zero_free (Seq.slice s 1 (Seq.length s)));
    split_cstr_append (Seq.slice s 1 (Seq.length s)) rest;  (* IH *)
    SP.cons_head_tail s;                    (* s == cons (head s) (tail s) *)
    assert (Seq.length full > 0);
    assert (Seq.index full 0 <> 0uy)
  end
#pop-options

(* ───────────────────────────────────────────────────────────────────────────
   The `Pulse.Lib.Protocol.WireFormat` round-trip law.
   ─────────────────────────────────────────────────────────────────────────── *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_tftp_parse_serialize_exact (m:tftp_message)
  : Lemma
      (ensures
        exists parsed.
          tftp_parse (tftp_serialize m) == Some (parsed, Seq.empty) /\
          parsed == m)
=
  match m with
  | Msg_rrq fn md ->
    let tail2 = Seq.append md (Seq.cons 0uy Seq.empty) in
    let body = Seq.append fn (Seq.cons 0uy tail2) in
    SP.append_slices (enc16 op_rrq) body;
    split_cstr_append fn tail2;
    split_cstr_append md Seq.empty
  | Msg_wrq fn md ->
    let tail2 = Seq.append md (Seq.cons 0uy Seq.empty) in
    let body = Seq.append fn (Seq.cons 0uy tail2) in
    SP.append_slices (enc16 op_wrq) body;
    split_cstr_append fn tail2;
    split_cstr_append md Seq.empty
  | Msg_data blk pl ->
    SP.append_slices (enc16 op_data) (Seq.append (enc16 blk) pl);
    SP.append_slices (enc16 blk) pl
  | Msg_ack blk ->
    SP.append_slices (enc16 op_ack) (enc16 blk);
    Seq.append_empty_r (enc16 blk);
    SP.append_slices (enc16 blk) Seq.empty
  | Msg_error code em ->
    let body = Seq.append (enc16 code) (Seq.append em (Seq.cons 0uy Seq.empty)) in
    SP.append_slices (enc16 op_error) body;
    SP.append_slices (enc16 code) (Seq.append em (Seq.cons 0uy Seq.empty));
    split_cstr_append em Seq.empty
#pop-options

(* ───────────────────────────────────────────────────────────────────────────
   The `Pulse.Lib.Protocol.WireFormat.wire_format` instance.

   NOTE: no `wire_format_stream_laws` instance — DATA is datagram-delimited and
   thus not a strong (prefix) parser (see the module docstring).
   ─────────────────────────────────────────────────────────────────────────── *)
noextract
let tftp_wire_format : WF.wire_format tftp_message =
{
  WF.wf_serialize = tftp_serialize;
  WF.wf_parse = tftp_parse;
  WF.wf_parse_serialize_exact = lemma_tftp_parse_serialize_exact;
}

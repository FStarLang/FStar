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
module MessagesParsing

open FStar.Mul
open FStar.HyperStack
open FStar.HST
open FStar.UInt32
open FStar.Int.Cast
open FStar.Buffer
open Messages2

#set-options "--lax"


(* Returns the length as a UInt32 *)
val read_length: b:bytes -> n:UInt32.t{v n = 1 \/ v n = 2 \/ v n = 3} -> STL UInt32.t
  (requires (fun h -> live h b /\ v n <= length b))
  (ensures  (fun h0 z h1 -> h1 == h0 ))
let read_length b n =
  if n = 1ul then (
    let b0 = index b 0ul in
    uint8_to_uint32 b0
  ) else if n = 2ul then (
    let b1 = index b 0ul in
    let b0 = index b 1ul in
    let b0 = uint8_to_uint32 b0 in
    let b1 = uint8_to_uint32 b1 in
    b0 |^ (b1 <<^ 8ul)
  ) else (
    let b2 = index b 0ul in
    let b1 = index b 1ul in
    let b0 = index b 2ul in
    let b0 = uint8_to_uint32 b0 in
    let b1 = uint8_to_uint32 b1 in
    let b2 = uint8_to_uint32 b2 in
    b0 |^ (b1 <<^ 8ul) |^ (b2 <<^ 16ul)
  )

val write_length: len:UInt32.t -> b:bytes -> n:UInt32.t{(v n = 1 \/ v n = 2 \/ v n = 3) /\ v len < pow2 (8 * v n) /\ length b >= v n} -> Stl unit
let write_length len b n =
  if n = 1ul then (
    let b0 = uint32_to_uint8 len in
    write b 0ul b0
  ) else if n = 2ul then (
    let b1 = uint32_to_uint8 len in
    let b0 = uint32_to_uint8 (shift_right len 8ul) in
    write b 0ul b0;
    write b 1ul b1
  ) else (
    let b2 = uint32_to_uint8 (shift_right len 0ul) in
    let b1 = uint32_to_uint8 (shift_right len 8ul) in
    let b0 = uint32_to_uint8 (shift_right len 16ul) in
    write b 0ul b0;
    write b 1ul b1;
    write b 2ul b2
  )

(* Generic parsing function for all types *)
let parse_type (t:sized_type) = b:bytes -> STL t
  (requires (fun h -> live h b))
  (ensures  (fun h0 z h1 -> h1 == h0 /\ z = inflate t (Seq.slice (as_seq h0 b) 0 (sizeof t))))

(* Implementations *)
let parse_buf_var #t len_bytes : parse_type (buf_var (v len_bytes) t) = fun b ->
  let l = read_length b len_bytes in
  let len = sub b 0ul len_bytes in
  let content = sub b len_bytes l in
  {b_length = len; b_content = content}

let parse_key_share : parse_type key_share = fun b ->
  let gn = sub b 0ul 2ul in
  let b = offset b 2ul in
  let pk = parse_buf_var #UInt8.t 2ul b in
  {ks_group_name = gn; ks_public_key = pk}

(* Generic parsing for arraybuf_var type *)
let parse_arraybuf_var #t t_bytes (p:parse_type t) len_bytes : parse_type (arraybuf_var (v len_bytes) t) = fun b ->
  let ab_length = sub b 0ul len_bytes in
  let l = read_length ab_length len_bytes in
  let l = UInt32.div l (UInt32.uint_to_t (sizeof t)) in
  let b = offset b len_bytes in
  let rec parse_arraybuf_var_aux (t_bytes:buffer t) (p:parse_type t) (b:bytes) (len:UInt32.t) : STL unit
    (requires (fun h -> live h t_bytes /\ live h b /\ disjoint b t_bytes /\ v len <= length b))
    (ensures  (fun h0 _ h1 -> modifies_1 t_bytes h0 h1 /\ live h1 t_bytes))
  = if UInt32.lt len (UInt32.uint_to_t (sizeof t)) then ()
    else (
      let z = p b in
      write t_bytes 0ul z;
      let b = offset b (UInt32.uint_to_t (sizeof t)) in
      let t_bytes = offset t_bytes 1ul in
      parse_arraybuf_var_aux t_bytes p b (len -^ l)
    ) in
  parse_arraybuf_var_aux t_bytes p b l;
  {abv_length = ab_length; abv_content = t_bytes}

let parse_arraybuf_var_key_share ks_bytes len_bytes : parse_type (arraybuf_var (v len_bytes) key_share) = fun b ->
  let ab_length = sub b 0ul len_bytes in
  let l = read_length ab_length len_bytes in
  let l = UInt32.div l (UInt32.uint_to_t (sizeof key_share)) in
  let b = offset b len_bytes in
  let rec parse_arraybuf_var_aux (ks_bytes:buffer key_share) (b:bytes) (len:UInt32.t) : STL unit
    (requires (fun h -> live h ks_bytes /\ live h b /\ disjoint b ks_bytes /\ v len <= length b))
    (ensures  (fun h0 _ h1 -> modifies_1 ks_bytes h0 h1 /\ live h1 ks_bytes))
  = if UInt32.lt len (UInt32.uint_to_t (sizeof key_share)) then ()
    else (
      let z = parse_key_share b in
      write ks_bytes 0ul z;
      let b = offset b (UInt32.uint_to_t (sizeof key_share)) in
      let t_bytes = offset ks_bytes 1ul in
      parse_arraybuf_var_aux ks_bytes b (len -^ l)
    ) in
  parse_arraybuf_var_aux ks_bytes b l;
  {abv_length = ab_length; abv_content = ks_bytes}

let parse_arraybuf_var_buf_var #t len_bv bv_bytes len_bytes : parse_type (arraybuf_var (v len_bytes) (buf_var (v len_bv) t)) = fun b ->
  let ab_length = sub b 0ul len_bytes in
  let l = read_length ab_length len_bytes in
  let l = UInt32.div l (UInt32.uint_to_t (sizeof (buf_var (v len_bv) t))) in
  let b = offset b len_bytes in
  let rec parse_arraybuf_var_aux (bv_bytes:buffer (buf_var (v len_bv) t)) (b:bytes) (len:UInt32.t) : STL unit
    (requires (fun h -> live h bv_bytes /\ live h b /\ disjoint b bv_bytes /\ v len <= length b))
    (ensures  (fun h0 _ h1 -> modifies_1 bv_bytes h0 h1 /\ live h1 bv_bytes))
  = if UInt32.lt len (UInt32.uint_to_t (sizeof (buf_var (v len_bv) t))) then ()
    else (
      let z = parse_buf_var #t len_bv b in
      write bv_bytes 0ul z;
      let b = offset b (UInt32.uint_to_t (sizeof (buf_var (v len_bv) t))) in
      let t_bytes = offset bv_bytes 1ul in
      parse_arraybuf_var_aux bv_bytes b (len -^ l)
    ) in
  parse_arraybuf_var_aux bv_bytes b l;
  {abv_length = ab_length; abv_content = bv_bytes}

val parse_client_extension: b:buffer client_extension -> ks_buf:buffer key_share -> psk_buf:buffer (buf_var 2 UInt8.t) -> sn_buf:buffer (buf_var 2 UInt8.t) -> exts:bytes -> len:UInt32.t -> STL bool
  (requires (fun h -> live h exts /\ live h ks_buf /\ live h psk_buf /\ live h sn_buf /\ v len <= length exts))
  (ensures  (fun h0 e h1 -> True))
let rec parse_client_extension b ks_buf psk_buf sn_buf exts len =
  if UInt32.lt len 4ul then false
  else (
    let (ext_type:buf UInt16.t 1) = sub exts 0ul 2ul in
    let (ext_typ:UInt16.t) = read (ptr_cast UInt16.t ext_type) 0ul in
    let l = read_length (offset exts 2ul) 2ul in
    let payload = offset exts 4ul in
    let (e:option client_extension) =
      if ext_typ = 0x01us then Some CE_extended_ms
      else if ext_typ = 0x02us then Some (CE_secure_renegotiation (parse_buf_var #UInt8.t 1ul payload))
      else if ext_typ = 0x03us then Some (CE_supported_groups (parse_buf_var #UInt16.t 2ul payload))
      else if ext_typ = 0x04us then Some (CE_supported_point_formats (parse_buf_var #UInt8.t 1ul payload))
      else if ext_typ = 0x05us then Some (CE_signature_algorithms (parse_buf_var #UInt16.t 2ul payload))
      else if ext_typ = 0x06us then Some (CE_earlyData)
      else if ext_typ = 0x07us then Some (CE_keyShare (parse_arraybuf_var_key_share ks_buf 2ul payload))
      else if ext_typ = 0x08us then Some (CE_preSharedKey (parse_arraybuf_var_buf_var #UInt8.t 2ul psk_buf 2ul payload))
      else if ext_typ = 0x09us then Some (CE_server_names (parse_arraybuf_var_buf_var #UInt8.t 2ul sn_buf 2ul payload))
      else None in
    match e with
    | Some e -> (
	write b 0ul e;
	let b = offset b 1ul in
	let exts = offset payload l in
	parse_client_extension b ks_buf psk_buf sn_buf exts (len -^ (4ul +^ l))
      )
    | None -> false
  )

let parse_arraybuf_var_client_extension ce_bytes ks_bytes psk_bytes sn_bytes len_bytes : parse_type (arraybuf_var (v len_bytes) client_extension) = fun b ->
  let ab_length = sub b 0ul len_bytes in
  let l = read_length ab_length len_bytes in
  let l = UInt32.div l (UInt32.uint_to_t (sizeof client_extension)) in
  let b = offset b len_bytes in
  let rec parse_arraybuf_var_aux (ce_bytes:buffer client_extension) (b:bytes) (len:UInt32.t) : STL unit
    (requires (fun h -> live h ce_bytes /\ live h b /\ disjoint b ce_bytes /\ v len <= length b))
    (ensures  (fun h0 _ h1 -> modifies_1 ce_bytes h0 h1 /\ live h1 ce_bytes))
  = if UInt32.lt len (UInt32.uint_to_t (sizeof client_extension)) then ()
    else (
      // Assume only one extension each otherwise incrementing the other buffers would be necessary
      let _ = parse_client_extension ce_bytes ks_bytes psk_bytes sn_bytes b in
      // The number of bytes parsed should be returned somehow
      let length_parsed_bytes = magic() in
      let b = offset b length_parsed_bytes in
      let ce_bytes = offset ce_bytes 1ul in
      parse_arraybuf_var_aux ce_bytes b (len -^ l)
    ) in
  parse_arraybuf_var_aux ce_bytes b l;
  {abv_length = ab_length; abv_content = ce_bytes}

val parse_client_hello: 
  msg:bytes -> len:UInt32.t{v len >= length msg} -> 
  buf:bytes ->   
  ce_buf:buffer client_extension -> 
  ks_buf:buffer key_share ->
  psk_buf:buffer (buf_var 2 UInt8.t) -> 
  sn_buf:buffer (buf_var 2 UInt8.t) -> STL (option ch)
  (requires (fun h -> live h msg /\ live h ce_buf /\ live h ks_buf /\ live h psk_buf /\ live h sn_buf))
  (ensures  (fun h0 _ h1 -> True))
let parse_client_hello msg len buf ce_buf ks_buf psk_buf sn_buf =
  let len' = len in
  if UInt32.lt len 35ul then None
  else (
    let pv = sub msg 0ul 2ul in
    let crand = sub msg 2ul 32ul in
    (* SID *)
    (* let sid = parse_buf_var 1 1 in // Need to get the length again if done that way *)
    let b = offset msg 34ul in
    let len_bytes = 1ul in
    let l = read_length b len_bytes in
    let len = sub b 0ul len_bytes in
    let content = sub b len_bytes l in
    let sid = {b_length = len; b_content = content} in    
    (* CS *)
    let b = offset b (l+^1ul) in
    let len_bytes = 2ul in
    let l' = read_length b len_bytes in
    let len = sub b 0ul len_bytes in
    let content = sub b len_bytes l' in
    let cs = {b_length = len; b_content = content} in    
    (* Compressions *)
    let b = offset b (l+^2ul) in
    let len_bytes = 1ul in
    let l'' = read_length b len_bytes in
    let len = sub b 0ul len_bytes in
    let content = sub b len_bytes l'' in
    let compressions = {b_length = len; b_content = content} in    
    (* Extensions *)
    // Assume that there are extensions for now
    let consumed_length = 2ul +^ 32ul +^ l +^ l' +^ l'' in
    (* if consumed_length =^ len then  *)
    let b = offset b (l''+^2ul) in
    let exts = parse_arraybuf_var_client_extension ce_buf ks_buf psk_buf sn_buf (len' -^ consumed_length) b in
    Some ({ch_protocol_version = pv; 
      ch_client_random = crand; 
      ch_sessionID = sid;
      ch_cipher_suites = cs; 
      ch_compressions = compressions; 
      ch_extensions = exts})
  )

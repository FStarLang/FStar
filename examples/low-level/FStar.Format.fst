module FStar.Format

open FStar.Ghost
open FStar.UInt8
open FStar.UInt32
open FStar.Int.Cast
open FStar.Seq
open FStar.ImmBuffer

type lsize = n:int{n = 1 \/ n = 2 \/ n = 3}
type csize = n:t{v n = 1 \/ v n = 2 \/ v n = 3}

val read_length: 
  b:buffer u8 -> 
  n:csize{v n <= length b} -> 
  Tot UInt32.t
let read_length b n =
  if n = 1ul then (
    let b0 = read b 0ul in
    uint8_to_uint32 b0
  ) else if n = 2ul then (
    let b1 = read b 0ul in
    let b0 = read b 1ul in
    let b0 = uint8_to_uint32 b0 in
    let b1 = uint8_to_uint32 b1 in
    b0 |^ (b1 <<^ 8ul)
  ) else (
    let b2 = read b 0ul in
    let b1 = read b 1ul in
    let b0 = read b 2ul in
    let b0 = uint8_to_uint32 b0 in
    let b1 = uint8_to_uint32 b1 in
    let b2 = uint8_to_uint32 b2 in
    b0 |^ (b1 <<^ 8ul) |^ (b2 <<^ 16ul)
  )

let vlbytes (n:lsize) = b:buffer u8{length b >= n /\ length b = n + v (read_length b (uint_to_t n))}

val vlparse: b:buffer u8 -> n:csize -> len:UInt32.t{v len < length b} -> Tot (result (vlbytes (v n)))
let vlparse b n len =
  if n >^ len then Error "Too short"
  else 
    let l = read_length b n in
    if length b < v n + v l then Error "Wrong vlbytes format"
    else (
      let b' = sub b 0ul (n +^ l) in
      Correct b'
    )

#set-options "--lax"

val vlsplit: b:buffer u8 -> n:csize -> len:UInt32.t{v len < length b} ->
  Tot (result (vlbytes (v n) * buffer u8))
let vlsplit b n len =
  if n >^ len then Error "Too short"
  else 
    let l = read_length b n in
    assume (v l + v n < pow2 32);
    if len <^ n +^ l then Error "Wrong vlbytes format"
    else (
      let b' = sub b 0ul (n +^ l) in
      let b'' = offset b (n +^ l) in
      Correct (b', b'') 
    )

val lemma_vlsplit: b:buffer u8 -> n:csize -> len:UInt32.t{v len < length b} ->
  Lemma 
    (requires (is_Correct (vlsplit b n len)))
    (ensures  (let t = vlsplit b n len in 
      (is_Correct t /\ (let t = correct t in 
	Seq.append (as_seq (fst t)) (as_seq (snd t)) == as_seq b))))
let lemma_vlsplit b n = admit() // TODO

type buf (#ty:sizeof_t) (t:serializable ty) (n:lsize) = b:buffer t{length b = n}

(* let vlbuf (#ty:sizeof_t) (n:lsize) (t:serializable t) = *)
(*   (l:buffer u8{length l = n} &  b:buffer t{length b = v (read_length l (uint_to_t n))}) *)

let vlbuf (#ty:sizeof_t) (n:lsize) (t:serializable ty) =
  b:buffer u8{length b >= n
    /\ (let content = Seq.slice (as_seq_bytes b) n (bytes_length b) in
      
      Seq.length content % sizeof ty = 0 /\ is_Correct (of_seq_bytes #ty #t content))}

assume val vlbuf_parse: #ty:sizeof_t -> t:serializable ty -> b:buffer u8 -> n:csize{length b >= v n} -> 
  Tot (result (vlbuf (v n) t))

assume val vlbuf_split: #ty:sizeof_t -> t:serializable ty -> b:buffer u8 -> n:csize{length b >= v n} -> 
  Tot (result (vlbuf (v n) t * buffer u8))

assume BufHasSize: forall (#ty:sizeof_t) (t:serializable ty) (n:lsize).
  hasSize (buf #ty t n) /\ sizeof (buf #ty t n) = sizeof (buffer t)

assume VlbytesHasSize: forall (n:lsize).
  hasSize (vlbytes n) /\ sizeof (vlbytes n) = sizeof (buffer u8)

assume VlbufHasSize: forall (#ty:sizeof_t) (t:serializable ty) (n:lsize).
  hasSize (vlbuf #ty n t) /\ sizeof (vlbuf #ty n t) = sizeof (buffer t)

assume val serialize_ptr: serializer bytes
assume val parse_ptr: parser serialize_ptr

noeq type key_share = {
  ks_group_name: buf u16 1;
  ks_public_key: vlbytes 2
}

assume KeyShareHasSize: 
  hasSize key_share /\ sizeof key_share = sizeof (buf u16 1) + sizeof (vlbytes 2)

let serialize_key_share: serializer key_share =
  admit();
  fun (ks:key_share) ->
    serialize_ptr ks.ks_group_name @| serialize_ptr ks.ks_public_key

#set-options "--lax"

let parse_key_share_bytes (b:bytes) (len:UInt32.t) : Tot (result key_share) =
  if len <^ 4ul then Error "Too short"
  else let ks_group_name = cast u16 u8 (sub (to_buffer u8 b) 0ul 2ul) in
       let ks_public_key = offset (to_buffer u8 b) 2ul in       
       match vlparse ks_public_key 2ul (len -^ 2ul) with
       | Correct x ->
	 Correct ({ks_group_name = ks_group_name; ks_public_key = x})
       | Error z -> Error z

let parse_key_share: parser serialize_key_share = fun s ->
  if Seq.length <> sizeof key_share then Error "Wrong pointer value"
  else (
    match parse_ptr with
    | Correct x ->  
    | Error z
  )

let key_share_bytes (ks:key_share) : Tot (seq byte) =
  as_seq_bytes (to_bytes ks.ks_group_name) @| as_seq_bytes (to_bytes ks.ks_public_key)

let key_share' = Serializable key_share seri

let key_share_ext = vlbuf 2 key_share

let parse_key_share_ext_bytes (kse:key_share_ext) =
  let 

noeq type client_extension =
 | CE_extended_ms
 | CE_secure_renegotiation of buf_var 1 u8
 | CE_supported_groups of buf_var 2 u16
 | CE_supported_point_formats of buf_var 1 u8
 | CE_signature_algorithms of buf_var 2 u16
 | CE_earlyData
 | CE_keyShare of arraybuf_var 2 key_share
 | CE_preSharedKey of arraybuf_var 2 (buf_var 2 u8)
 | CE_server_names of arraybuf_var 2 (buf_var 2 u8)

type ch =  {
  ch_protocol_version:buf u16 1;
  ch_client_random:buf u8 32;
  ch_sessionID:buf_var 1 u8;
  ch_cipher_suites:buf_var 2 u16;
  ch_compressions:buf_var 1 u8;
  ch_extensions:arraybuf_var 2 client_extension;
}


(* type c_extensions = { *)
(*   ce_extended_ms: byte; *)
(*   ce_secure_renegotiation: buf_var 1 1; *)
(*   ce_supported_groups: buf_var 2 2; *)
(*   ce_supported_point_formats: buf_var 1 1; *)
(*   ce_signature_algorithms: buf_var 2 2; *)
(*   ce_earlyData: byte; *)
(*   ce_keyShare: key_share *)
(*   ce_preSharedKey: arraybuf_var 2 (buf_var 2 1) *)
(*   ce_server_names: arraybuf_var 2 (buf_var 2 1) *)
(* } *)

(* type c_hello = { *)
(*   c_protocol_version:buf 2 1; *)
(*   c_client_random:buf 1 32; *)
(*   ch_sessionID:buf_var 1 1; *)
(*   ch_cipher_suites:buf_var 2 2; *)
(*   ch_compressions:buf_var 1 1; *)
(*   ch_extensions:arraybuf_var 2 client_extension; *)
(* } *)

(*
let clientHelloBytes ch buf = ...
  
  *)

type server_extension =
 | SE_extended_ms
 | SE_secure_renegotiation of buf_var 1 u8
 | SE_supported_point_formats of buf_var 1 u8
 | SE_earlyData
 | SE_keyShare of key_share
 | SE_preSharedKey of buf_var 2 u8
 | SE_server_names

type sh =  {
  sh_protocol_version:buf u16 1;
  sh_client_random:buf u8 32;
  sh_sessionID:option (buf_var 1 u8);
  sh_cipher_suites:buf_var 2 u16;
  sh_compressions:option (buf_var 1 u8);
  sh_extensions:arraybuf_var 2 server_extension;
}

(*
struct
{ version : buf 1 short;
  random:   buf 32 short;
  sessionid: buf_var 1 byte;
  ciphersuites: buf_var 2 short;
  compressions: buf_var 1 byte;
  extensions:   buf_var 2
    struct {
      name: buf 1 short;
      payload: buf_var 2
         union {
  	   empty;
	   buf_var 1 bytte;
	   |
      list <struct [buf 2 1; buf_var 2 1]>
            
    >
   >
  ]
*)

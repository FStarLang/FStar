module Messages3

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open FStar.UInt32
open FStar.Int.Cast
open FStar.Buffer
open Low.Bytes

type buf (t:serializable) (n:nat) = b:(buffer t){length b = op_Multiply (sizeof t) n}

type buf_var (len_bytes:nat) (t:serializable) =
     {b_length: buf UInt8.t len_bytes;
      b_content: buffer UInt8.t}

type arraybuf_var (len_bytes:nat) (t:serializable) =
     {ab_length: buf UInt8.t len_bytes;
      ab_content: buffer t}

type key_share = {
  ks_group_name: buf UInt16.t 1;
  ks_public_key: buf_var 2 UInt8.t
}

type client_extension =
 | CE_extended_ms
 | CE_secure_renegotiation of buf_var 1 UInt8.t
 | CE_supported_groups of buf_var 2 UInt16.t
 | CE_supported_point_formats of buf_var 1 UInt8.t
 | CE_signature_algorithms of buf_var 2 UInt16.t
 | CE_earlyData
 | CE_keyShare of arraybuf_var 2 key_share
 | CE_preSharedKey of arraybuf_var 2 (buf_var 2 UInt8.t)
 | CE_server_names of arraybuf_var 2 (buf_var 2 UInt8.t)

type ch =  {
  ch_protocol_version:buf UInt16.t 1;
  ch_client_random:buf UInt8.t 32;
  ch_sessionID:buf_var 1 UInt8.t;
  ch_cipher_suites:buf_var 2 UInt16.t;
  ch_compressions:buf_var 1 UInt8.t;
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
 | SE_secure_renegotiation of buf_var 1 UInt8.t
 | SE_supported_point_formats of buf_var 1 UInt8.t
 | SE_earlyData
 | SE_keyShare of key_share
 | SE_preSharedKey of buf_var 2 UInt8.t
 | SE_server_names

type sh =  {
  sh_protocol_version:buf UInt16.t 1;
  sh_client_random:buf UInt8.t 32;
  sh_sessionID:option (buf_var 1 UInt8.t);
  sh_cipher_suites:buf_var 2 UInt16.t;
  sh_compressions:option (buf_var 1 UInt8.t);
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

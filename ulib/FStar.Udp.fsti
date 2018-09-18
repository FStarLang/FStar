module FStar.Udp
open FStar.Bytes
open FStar.Error

(* Type declarations *)
new
val socket: eqtype
new
val sock_in_channel: Type0
new
val sock_out_channel: Type0
new
val udpListener: Type0

(* Server side *)
val listen: string -> nat -> EXT udpListener
val accept: udpListener -> EXT socket
val stop: udpListener -> EXT unit

(* Client side *)
val connect: string -> nat -> EXT socket

(* Input/Output *)
val recv: socket -> nat -> EXT (optResult string bytes)
val send: socket -> bytes -> EXT (optResult string unit)
val close: socket -> EXT unit

(* Helper functions *)
val socket_split: socket -> EXT (sock_in_channel * sock_out_channel)
val flush: sock_out_channel -> EXT unit

(* Unimplemented *)
//assume val connectTimeout: nat -> string -> nat -> EXT socket
//assume val acceptTimeout: nat -> tcpListener -> EXT socket
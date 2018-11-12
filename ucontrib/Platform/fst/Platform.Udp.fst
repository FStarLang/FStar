module Platform.Udp

open FStar.HyperHeap

open Platform.Bytes
open Platform.Error


(* Type declarations *)
assume new type socket: Type0
assume new type sock_in_channel: Type0
assume new type sock_out_channel: Type0
assume new type udpListener: Type0

// Equality of sockets
assume HasEq_socket: hasEq socket

(* Server side *)
assume val listen: string -> nat -> EXT udpListener
assume val accept: udpListener -> EXT socket
assume val stop: udpListener -> EXT unit

(* Client side *)
assume val connect: string -> nat -> EXT socket

(* Input/Output *)
assume val recv: socket -> nat -> EXT (optResult string bytes)
assume val send: socket -> bytes -> EXT (optResult string unit)
assume val close: socket -> EXT unit

(* Helper functions *)
assume val socket_split: socket -> EXT (sock_in_channel * sock_out_channel)
assume val flush: sock_out_channel -> EXT unit

(* Unimplemented *)
//assume val connectTimeout: nat -> string -> nat -> EXT socket
//assume val acceptTimeout: nat -> tcpListener -> EXT socket

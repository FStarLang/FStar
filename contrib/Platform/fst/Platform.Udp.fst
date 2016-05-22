module Platform.Udp

open FStar.Heap
open FStar.HyperHeap

open Platform.Bytes
open Platform.Error


(* Type declarations *)

type socket
type sock_in_channel
type sock_out_channel
type udpListener

(* This library is used by miTLS; for now we model external calls as
   stateful but with no effect on the heap; we could be more precise,
   e.g. specify that they modify some private network region, and that
   socket should not be accessed after an error. *)

effect EXT (a:Type) = ST a
  (requires (fun _ -> True))
  (ensures (fun h0 _ h -> modifies Set.empty h0 h))

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

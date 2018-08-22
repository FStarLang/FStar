module FStar.Tcp

open FStar.Bytes
open FStar.Error

new val networkStream: eqtype
new val tcpListener: Type0

val set_nonblock: networkStream -> unit
val clear_nonblock: networkStream -> unit

(* Server side *)

val listen: string -> nat -> EXT tcpListener
val acceptTimeout: nat -> tcpListener -> EXT networkStream
val accept: tcpListener -> EXT networkStream
val stop: tcpListener -> EXT unit

(* Client side *)

val connectTimeout: nat -> string -> nat -> EXT networkStream
val connect: string -> nat -> EXT networkStream

(* Input/Output *)

// adding support for (potentially) non-blocking I/O
// NB for now, send *fails* on partial writes, and *loops* on EAGAIN/EWOULDBLOCK.

type recv_result (max:nat) = 
  | RecvWouldBlock
  | RecvError of string
  | Received of b:bytes {length b <= max}
val recv_async: networkStream -> max:nat -> EXT (recv_result max)

val recv: networkStream -> max:nat -> EXT (optResult string (b:bytes {length b <= max}))
val send: networkStream -> bytes -> EXT (optResult string unit)
val close: networkStream -> EXT unit

(* Create a network stream from a given stream.
   Only used by the application interface TLSharp. *)
(* assume val create: System.IO.Stream -> NetworkStream*)

 

module Platform.Tcp
open Platform.Bytes
open Platform.Error

type networkStream 
type tcpListener 

(* Create a network stream from a given stream.
   Only used by the application interface TLSharp. *)
(* assume val create: System.IO.Stream -> NetworkStream*)

(* Server side *)

assume val listen: string -> int -> tcpListener
assume val acceptTimeout: int -> tcpListener -> networkStream
assume val accept: tcpListener -> networkStream
assume val stop: tcpListener -> unit

(* Client side *)

assume val connectTimeout: int -> string -> int -> networkStream
assume val connect: string -> int -> networkStream

(* Input/Output *)

assume val read: networkStream -> int -> optResult string bytes
assume val write: networkStream -> bytes -> optResult string unit
assume val close: networkStream -> unit

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

 

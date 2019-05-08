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

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
module FStar.Udp
open FStar.Bytes
open FStar.Error

(* Type declarations *)
new val socket: eqtype
new val sock_in_channel: Type0
new val sock_out_channel: Type0
new val udpListener: Type0

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
val socket_split: socket -> EXT (sock_in_channel & sock_out_channel)
val flush: sock_out_channel -> EXT unit

(* Unimplemented *)
//assume val connectTimeout: nat -> string -> nat -> EXT socket
//assume val acceptTimeout: nat -> tcpListener -> EXT socket

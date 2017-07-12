module FStar.Tcp
open FStar.Bytes
open FStar.All

assume new type stream
assume new type listener


(* Server side *)

assume val listen: host:string -> port:int -> ML listener
assume val accept: l:listener -> ML stream
assume val stop: l:listener -> ML unit

(* Client side *)

assume val connect: host:string -> port:int -> ML stream

(* Input/Output *)

assume val read: s:stream -> n:int -> ML (option bytes)
assume val write: s:stream -> b:bytes -> ML (option unit)
assume val close: s:stream -> ML unit

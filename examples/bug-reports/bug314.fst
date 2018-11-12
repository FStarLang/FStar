module Bug314

open FStar.All
open FStar.String
open FStar.IO

(* two events, recording genuine requests and responses *)

type lnat = nat


val escape : lnat -> Tot nat
let escape l = l


assume new type request : string -> Type
assume new type response : string -> string -> Type

(* the meaning of MACs, as used in RPC *)

type reqresp (msg:string) = (exists s. request s)

module Bug

open FStar.All
open FStar.String
open FStar.IO

(* two events, recording genuine requests and responses *)

logic type lnat = nat


val escape : lnat -> Tot nat
let escape l = l


(* logic *) type Request : string -> Type
(* logic *) type Response : string -> string -> Type

(* the meaning of MACs, as used in RPC *)

(* opaque logic *) type reqresp (msg:string) =
    (exists s.    Request s)
(* \/ (exists s t.  Response s t) *)

(*
let keygen (p: (string -> Type)) =
  ()


let k = print_string "generating shared key...\n";
  keygen reqresp*)

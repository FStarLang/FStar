(* Copyright (c) Microsoft Corporation.  All rights reserved.  *)

module RPC
open Array
open SHA1
open Formatting
open MAC

(* some basic, untrusted network controlled by the adversary *)

val send: message -> unit
let send m = magic()
val recv: (message -> unit) -> unit
let recv m = magic()

(* two events, recording genuine requests and responses *)

logic type Request : string -> Type
logic type Response : string -> string -> Type

(* the meaning of MACs, as used in RPC *)

opaque logic type reqresp (msg:message) =
    (exists s.   msg = Formatting.request s    /\ Request s)
 \/ (exists s t. msg = Formatting.response s t /\ Response s t)

let k = keygen reqresp 

let client (s:string16) =
  assume (Request s);
  send (append (utf8 s) (mac k (Formatting.request s))); 
  recv (fun msg ->
    if length msg < macsize then failwith "Too short"
    else
      let (v, m') = split msg (length msg - macsize) in
      let t = iutf8 v in
      if verify k (Formatting.response s t) m'
      then assert (Response s t))

let server () =
  recv (fun msg ->
    if length msg < macsize then failwith "Too short"
    else
      let (v,m) = split msg (length msg - macsize) in
      if length v > 65535 then failwith "Too long" 
      else
        let s = iutf8 v in
        if verify k (Formatting.request s) m 
        then  
          ( assert (Request s);
            let t = "22" in
            assume (Response s t);
            send (append (utf8 t) (mac k (Formatting.response s t)))))
  
(* 
let test () = 
  server(); 
  client "2 + 2? *)

(* Copyright (c) Microsoft Corporation.  All rights reserved.  *)

module RPC
open Array
open Format
open SHA1
open MAC

(* some basic, untrusted network controlled by the adversary *)

assume val send: message -> unit
assume val recv: (message -> unit) -> unit

(* two events, recording genuine requests and responses *)

logic type Request : string -> Type
logic type Response : string -> string -> Type

(* let k = keygen (fun msg -> (exists s. msg = request s /\ Request s) \/       *)
(*                            (exists s t. msg = response s t /\ Response s t)) *)
opaque logic type reqresp (msg:message) =
    (exists s. msg = request s /\ Request s)
      \/ (exists s t. msg = response s t /\ Response s t)

assume val k : pkey reqresp

let client (s:string16) =
  assume (Request s);
  send (append (utf8 s) (mac k (request s))); 
  recv (fun msg ->
    if length msg < macsize then failwith "Too short"
    else
      let (v, m') = split msg (length msg - macsize) in
      let t = iutf8 v in
      if verify k (response s t) m'
      then assert (Response s t))

let server () =
  recv (fun msg ->
    if length msg < macsize then failwith "Too short"
    else
      let (v,m) = split msg (length msg - macsize) in
      if length v > 65535 then failwith "Too long" 
      else
        let s = iutf8 v in
        if verify k (request s) m 
        then  
          ( assert (Request s);
            let t = "22" in
            assume (Response s t);
            send (append (utf8 t) (mac k (response s t)))))
  
(* 
let test () = 
  server(); 
  client "2 + 2? *)

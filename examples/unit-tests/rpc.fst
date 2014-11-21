(* Copyright (c) Microsoft Corporation.  All rights reserved.  *)
module RPC
open MacIdeal
open Format
open Array

assume val send: message -> unit
assume val recv: (message -> unit) -> unit
logic type Request : string -> Type
logic type Response : string -> string -> Type

(* let k = new_key (fun msg -> (exists s. msg = request s /\ Request s) \/       *)
(*                             (exists s t. msg = response s t /\ Response s t)) *)
opaque logic type reqresp (msg:message) =
    (exists s. msg = request s /\ Request s)
      \/ (exists s t. msg = response s t /\ Response s t)

assume val k : pkey reqresp

let client (s:string16) =
  assume (Request s);
  send (append (utf8 s) (mac k (request s))); 
  recv (fun msg ->
    if length msg < macsize
    then failwith "Too short"
    else
      let (v, m') = split msg (length msg - macsize) in
      let t = iutf8 v in
      if verify k (response s t) m'
      then assert (Response s t))

let server () =
  recv (fun msg ->
    if length msg < macsize
    then failwith "Too short"
    else
      let (v,m) = split msg (length msg - macsize) in
      let s = iutf8 v in
      if verify k (request s) m && length v < 65536 //NEEDED THIS CHECK to make a well-formed response
      then  (assert (Request s);
             let t = "22" in
             assume (Response s t);
             send (append (utf8 t) (mac k (response s t)))))
    

(* let test () = server(); client "2 + 2?" *)

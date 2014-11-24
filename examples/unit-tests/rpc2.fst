(* Copyright (c) Microsoft Corporation.  All rights reserved.  *)

(* a variant of RPC with multiple principals and partial compromise *)

module RPC
open Array
open Format
open MAC

(* some basic, untrusted network controlled by the adversary *)

assume val send: message -> unit
assume val recv: (message -> unit) -> unit

(* principals are just strings; they can be dynamically corrupted *)

type principal = string

logic type Corrupt: principal -> Type 

(* two events, recording genuine requests and responses *)

logic type Request : principal -> principal -> string -> Type
logic type Response : principal -> principal -> string -> string -> Type

(* let k = keygen (fun msg -> (exists s. msg = request s /\ Request s) \/       *)
(*                            (exists s t. msg = response s t /\ Response s t)) *)
opaque logic type reqresp (a:principal) (b:principal) (msg:message) =
    (exists s. msg = request s /\ Request a b s)
 \/ (exists s t. msg = response s t /\ Response a b s t)
 \/ Corrupt a \/ Corrupt b

assume val keys : a: principal -> b:principal -> pkey (reqresp a b)

let client a b (s:string16) =
  assume (Request a b s);
  let k = keys a b in
  send (append (utf8 s) (mac k (request s))); 
  recv (fun msg ->
    if length msg < macsize then failwith "Too short"
    else
      let (v, m') = split msg (length msg - macsize) in
      let t = iutf8 v in
      if verify k (response s t) m'
      then assert (Corrupt a \/ Corrupt b \/ Response a b s t))

let server a b =
  recv (fun msg ->
    if length msg < macsize then failwith "Too short"
    else
      let (v,m) = split msg (length msg - macsize) in
      if length v > 65535 then failwith "Too long" // we need this check to ensure a well-formed response
      else
        let s = iutf8 v in
        let k = keys a b in   // TODO hoisting this outside the closure breaks inference. 
        if verify k (request s) m 
        then  
          ( assert (Corrupt a \/ Corrupt b \/ Request a b s);
            let t = "22" in
            assume (Response a b s t);
            send (append (utf8 t) (mac k (response s t)))))
    
(* let test () = server(); client "2 + 2?" *)

(*--build-config
    options:--z3timeout 10 --verify_module RPC --admit_fsi FStar.Seq --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --admit_fsi FStar.IO;
    variables:CONTRIB=../../contrib;
    other-files:
            FStar.FunctionalExtensionality.fst FStar.Classical.fst
            FStar.Set.fsi FStar.Set.fst
            FStar.Heap.fst FStar.ST.fst FStar.All.fst
            FStar.String.fst FStar.List.fst
            seq.fsi FStar.SeqProperties.fst
            FStar.IO.fsti
            $CONTRIB/Platform/fst/Bytes.fst
            $CONTRIB/CoreCrypto/fst/CoreCrypto.fst
            formatting.fst
            sha1.fst
            mac.fst
  --*)


(* Copyright (c) Microsoft Corporation.  All rights reserved.  *)

module RPC

open FStar.All
open FStar.String
open FStar.IO


let init_print = print_string "\ninitializing...\n\n"

open Platform.Bytes
(*open Seq
open SeqProperties*)
open SHA1
open Formatting
open MAC

//does it verify for trivial reasons, like a bug in the build-config?
(*let testme () =
   assert False*)
   

(* some basic, untrusted network controlled by the adversary *)


(*let log_prot = ST.alloc []*)
val msg_buffer: ref message
let msg_buffer = ST.alloc (empty_bytes)

val send: message -> unit
let send m = msg_buffer := m
val recv: (message -> unit) -> unit
let rec recv call = if length !msg_buffer > 0
                then (
                  let msg = !msg_buffer in
                  msg_buffer := empty_bytes;
                  call msg)
                else recv call

(* two events, recording genuine requests and responses *)

logic type Request : string -> Type
logic type Response : string -> string -> Type

(* the meaning of MACs, as used in RPC *)

opaque logic type reqresp (msg:message) =
    (exists s.   msg = Formatting.request s    /\ Request s)
 \/ (exists s t. msg = Formatting.response s t /\ Response s t)

let k = print_string "generating shared key...\n";
  keygen reqresp


let client_send (s:string16) =
  assume (Request s);
  print_string "\nclient send:";
  print_string s;

  send ( (utf8 s) @| (mac k (Formatting.request s)))


let client_recv (s:string16) =
  recv (fun msg ->
    if length msg < macsize then failwith "Too short"
    else
      let (v, m') = split msg (length msg - macsize) in
      let t = iutf8 v in
      if verify k (Formatting.response s t) m'
      then (
        assert (Response s t);
        print_string "\nclient verified:";
        print_string t ))

let client (s:string16) =
  client_send s;
  client_recv s




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
            print_string "\nserver verified:";
            print_string s;
            let t = "42" in
            assume (Response s t);
            print_string "\nserver sent:";
            print_string t;
            send ( (utf8 t) @| (mac k (Formatting.response s t))))
        else failwith "Invalid MAC" )


let test () =
  let query = "4 + 2" in
  if length (utf8 query) > 65535 then failwith "Too long"
  else
    client_send query;
    server();
    client_recv query;
    print_string "\n\n"

let run = test ()
(* check_marker *)

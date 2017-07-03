module Ex12b.RPC
open FStar.ST
open FStar.All
open FStar.String
open FStar.IO


let init_print = print_string "\ninitializing...\n\n"

open Platform.Bytes
open Ex12.SHA1
open Ex12b.Format
open Ex12.MAC

module Formatting = Ex12b.Format

(* some basic, untrusted network controlled by the adversary *)


val msg_buffer: ref message
let msg_buffer = ST.alloc (empty_bytes)

// BEGIN: Network
val send: message -> ML unit
val recv: (message -> ML unit) -> ML unit
// END: Network

let send m = msg_buffer := m
let rec recv call = if length !msg_buffer > 0
                then (
                  let msg = !msg_buffer in
                  msg_buffer := empty_bytes;
                  call msg)
                else recv call

(* two events, recording genuine requests and responses *)

// BEGIN: RpcPredicates
assume type pRequest : string -> Type0
assume type pResponse : string -> string -> Type0
// END: RpcPredicates

(* the meaning of MACs, as used in RPC *)

// BEGIN: MsgProperty
type reqresp text = 
     (exists s.   text = Formatting.request  s   /\ pRequest s)
  \/ (exists s t. text = Formatting.response s t /\ pResponse s t)
// END: MsgProperty

(* FIXME: this type annotation is a workaround for #486 *)
val k: k:key{key_prop k == reqresp}
let k = print_string "generating shared key...\n";
  keygen reqresp


val client_send : string16 -> ML unit
let client_send (s:string16) =
  assume (pRequest s);
  print_string "\nclient send:";
  print_string s;

  assert(reqresp (Formatting.request s)); (* this works *)
  assert(key_prop k == reqresp);          (* this also works *)
  assert(key_prop k (Formatting.request s) == reqresp (Formatting.request s));
  (*assert(key_prop k (Formatting.request s)); -- this fails *)
  send ( (utf8 s) @| (mac k (Formatting.request s)))


val client_recv : string16 -> ML unit
let client_recv (s:string16) =
  recv (fun msg ->
    if length msg < macsize then failwith "Too short"
    else
      let (v, m') = split msg (length msg - macsize) in
      let t = iutf8 v in
      if verify k (Formatting.response s t) m'
      then (
        assert (pResponse s t);
        print_string "\nclient verified:";
        print_string t ))

// BEGIN: RpcProtocol
val client : string16 -> ML unit
let client (s:string16) =
  client_send s;
  client_recv s

val server : unit -> ML unit
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
          ( 
            assert (pRequest s);
            print_string "\nserver verified:";
            print_string s;
            let t = "42" in
            assume (pResponse s t);
            print_string "\nserver sent:";
            print_string t;
            send ( (utf8 t) @| (mac k (Formatting.response s t))))
        else failwith "Invalid MAC" )
// END: RpcProtocol

val test : unit -> ML unit
let test () =
  let query = "4 + 2" in
  if length (utf8 query) > 65535 then failwith "Too long"
  else
    client_send query;
    server();
    client_recv query;
    print_string "\n\n"

val run : unit
let run = test ()
(* check_marker *)

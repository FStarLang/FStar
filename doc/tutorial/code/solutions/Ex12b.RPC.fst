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
module Ex12b.RPC

open FStar.IO

open FStar.Preorder
open FStar.Heap
open FStar.ST
open FStar.All
open FStar.MRef

open FStar.List.Tot
open FStar.String


let init_print = print_string "\ninitializing...\n\n"

open FStar.Bytes
open Ex12.SHA1
open Ex12b2.Format
open Ex12.MAC


module Formatting = Ex12b2.Format

(** some basic, untrusted network controlled by the adversary *)
val msg_buffer: ref message
let msg_buffer = alloc (empty_bytes)

// BEGIN: Network
private val send: message -> St unit
private val recv: (message -> ML unit) -> ML unit
// END: Network

let send m = 
  msg_buffer := m

let rec recv call = 
  if length !msg_buffer > 0
  then (
    let msg = !msg_buffer in
    msg_buffer := empty_bytes;
    call msg)
  else recv call

(** two events, recording genuine requests and responses *)
type log_entry =
  | Request: string -> log_entry
  | Response: string -> string -> log_entry

let subset' (#a:eqtype) (l1:list a) (l2:list a)
  = (forall x. x `mem` l1 ==> x `mem` l2)
let subset (#a:eqtype) : Tot (preorder (list a)) = subset'

type lref = mref (list log_entry) subset

private let log : lref = alloc #_ #(subset #log_entry) []

let add_to_log (r:lref) (v:log_entry) :
      ST unit (requires (fun _ -> True))
              (ensures (fun _ _ h -> v `mem` (sel h r))) =
  r := (v :: !r)

// BEGIN: RpcPredicates
val pRequest : string -> Type0
val pResponse : string -> string -> Type0
// END: RpcPredicates

let req s : Tot (p:(list log_entry -> Type0){Preorder.stable p subset})
  = fun xs -> mem (Request s) xs
let resp s t : Tot (p:(list log_entry -> Type0){Preorder.stable p subset})
  = fun xs -> mem (Response s t) xs

let pRequest s = token log (req s)
let pResponse s t = token log (resp s t)

(* the meaning of MACs, as used in RPC *)

// BEGIN: MsgProperty
type reqresp text = 
     (exists s.   text = Formatting.request  s   /\ pRequest s )
  \/ (exists s t. text = Formatting.response s t /\ pResponse s t)
// END: MsgProperty

val k:pkey reqresp
let k = print_string "generating shared key...\n";
  keygen reqresp


val client_send : s:string16 -> ML unit
let client_send (s:string16) =
  print_string "\nclient send:";
  print_string s;
  add_to_log log (Request s);
  witness_token log (req s);

  assert(reqresp (Formatting.request s)); (* this works *)
  // assert(key_prop k == reqresp);          (* this also works *)
  assert (reqresp (Formatting.request s)) ;
  // assert(key_prop k (Formatting.request s));  (* this fails *) 
  send ( (utf8_encode s) @| (mac k (Formatting.request s)))


val client_recv : string16 -> ML unit
let client_recv (s:string16) =
  recv (fun msg ->
    if FStar.UInt32.(len msg <^ macsize) then failwith "Too short"
    else
      let (v, m') = split msg FStar.UInt32.(len msg -^ macsize) in
      match iutf8_opt v with      
      | Some t ->
        assert (String.length t < pow2 30);
        let m = Formatting.response s t in
        assume (UInt.fits (Bytes.length m) 31);
        if verify k m m'
        then (
          from_key_prop k (Formatting.response s t);
          assert (pResponse s t);
          recall_token log (resp s t);
          let xs = !log in
          assert (Response s t `mem` xs);
          print_string "\nclient verified:";
          print_string t)
      | None -> ()
  )


// BEGIN: RpcProtocol
val client : string16 -> ML unit
let client (s:string16) =
  client_send s;
  client_recv s

val server : unit -> ML unit
let server () =
  recv (fun msg ->
    if FStar.UInt32.(len msg <^ macsize) then failwith "Too short"
    else
      let (v,m) = split msg FStar.UInt32.(len msg -^ macsize) in
      if length v > 65535 then failwith "Too long"
      else
        match iutf8_opt v with 
        | Some s ->
          if verify k (Formatting.request s) m
          then
            (
              from_key_prop k (Formatting.request s);
              assert (pRequest s);
              recall_token log (req s);
              let xs = !log in
              assert (Request s `mem` xs);
              print_string "\nserver verified:";
              print_string s;
              let t = "42" in
              add_to_log log (Response s t);
              witness_token log (resp s t);
              print_string "\nserver sent:";
              print_string t;
              assume (String.length t < pow2 30);
              assume (String.length s < pow2 16);
              let rst = Formatting.response s t in
              assume (UInt.fits (length rst) 31);
              let et = utf8_encode t in 
              let mkr = mac k rst in
              assume (UInt.fits (Bytes.length et + Bytes.length mkr) 32);
              let st = Bytes.append et mkr  in
              assume (UInt.fits (Bytes.length st) 32);
              send (st)
              )
          else failwith "Invalid MAC" 
       | None -> ()
   )
// END: RpcProtocol

private val test : unit -> ML unit
let test () =
  let query = "4 + 2" in
  assume (String.length query < pow2 16);
  if length (utf8_encode query) > 65535 then failwith "Too long"
  else
    client_send query;
    server();
    client_recv query;
    print_string "\n\n"

val run : unit
let run = test ()
(* check_marker *)

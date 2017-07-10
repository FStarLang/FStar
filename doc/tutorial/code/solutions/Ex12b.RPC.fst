module Ex12b.RPC

(* open FStar.HyperStack.ST *)
(* open FStar.Seq *)
(* open FStar.Monotonic.Seq *)
(* open FStar.HyperHeap *)
(* open FStar.HyperStack *)
(* open FStar.Monotonic.RRef *)

open FStar.IO

open Preorder
open Heapx
open STx
open MRefx

open FStar.List.Tot
open FStar.String


let init_print = debug_print_string "\ninitializing...\n\n"

open Platform.Bytes
open Ex12.SHA1
open Ex12b2.Format
open Ex12.MAC


module Formatting = Ex12b2.Format

(* some basic, untrusted network controlled by the adversary *)


val msg_buffer: ref message
let msg_buffer = alloc _ (empty_bytes)

// BEGIN: Network
private val send: message -> St unit
private val recv: (message -> St unit) -> St unit
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

(* two events, recording genuine requests and responses *)


type log_entry = 
  | Request: string -> log_entry
  | Response: string -> string -> log_entry
  

(* private type log_t (r:rid) = Monotonic.Seq.log_t r log_entry *)
(* let log:log_t root = alloc_mref_seq #log_entry root createEmpty *)

let subset' (#a:eqtype) (l1:list a) (l2:list a)
  = (forall x. x `mem` l1 ==> x `mem` l2)
let subset (#a:eqtype) : Tot (preorder (list a)) = subset'

type lref = mref (list log_entry) subset

private let log : lref = alloc (subset #log_entry) []

let add_to_log (r:lref) (v:log_entry) :
      ST unit (requires (fun _ -> True))
              (ensures (fun _ _ h -> v `mem` (sel h r))) =
  r := (v :: !r)

// BEGIN: RpcPredicates

let req s : Tot (p:(list log_entry -> Type0){Preorder.stable p subset})
  = fun xs -> mem (Request s) xs
let resp s t : Tot (p:(list log_entry -> Type0){Preorder.stable p subset})
  = fun xs -> mem (Response s t) xs

type pRequest s = token log (req s)
type pResponse s t = token log (resp s t)
// END: RpcPredicates

(* the meaning of MACs, as used in RPC *)

// BEGIN: MsgProperty
type reqresp text = 
     (exists s.   text = Formatting.request  s   /\ pRequest s )
  \/ (exists s t. text = Formatting.response s t /\ pResponse s t)
// END: MsgProperty

val k: k:key{key_prop k == reqresp}
let k = ignore (debug_print_string "generating shared key...\n");
  keygen reqresp



val client_send : s:string16 -> St unit
let client_send (s:string16) =
  ignore (debug_print_string "\nclient send:");
  ignore (debug_print_string s);
  add_to_log log (Request s);
  witness log (req s);
  
  assert(reqresp (Formatting.request s)); (* this works *)
  assert(key_prop k == reqresp);          (* this also works *)
  assert(key_prop k (Formatting.request s) == reqresp (Formatting.request s));
  (*assert(key_prop k (Formatting.request s)); -- this fails *)
  send ( (utf8 s) @| (mac k (Formatting.request s)))


val client_recv : string16 -> St unit
let client_recv (s:string16) =
  recv (fun msg ->
    if length msg < macsize then ignore (debug_print_string "Too short")
    else
      let (v, m') = split msg (length msg - macsize) in
      let t = iutf8 v in
      if verify k (Formatting.response s t) m'
      then (
        assert (pResponse s t);
        recall log (resp s t);
        let xs = !log in
        assert (Response s t `mem` xs);
        ignore (debug_print_string "\nclient verified:");
        ignore (debug_print_string t) ))

// BEGIN: RpcProtocol
val client : string16 -> St unit
let client (s:string16) =
  client_send s;
  client_recv s

val server : unit -> St unit
let server () =
  recv (fun msg ->
    if length msg < macsize then ignore (debug_print_string "Too short")
    else
      let (v,m) = split msg (length msg - macsize) in
      if length v > 65535 then ignore (debug_print_string "Too long")
      else
        let s = iutf8 v in
        if verify k (Formatting.request s) m
        then
          (
            assert (pRequest s);
            recall log (req s);
            let xs = !log in
            assert (Request s `mem` xs);
            ignore (debug_print_string "\nserver verified:");
            ignore (debug_print_string s);
            let t = "42" in
            add_to_log log (Response s t);
            witness log (resp s t);
            ignore (debug_print_string "\nserver sent:");
            ignore (debug_print_string t);
            send ( (utf8 t) @| (mac k (Formatting.response s t)))
            )
        else ignore (debug_print_string "Invalid MAC" ))
// END: RpcProtocol

private val test : unit -> St unit
let test () =
  let query = "4 + 2" in
  if length (utf8 query) > 65535 then ignore (debug_print_string "Too long")
  else
    let query : string16 = query in
    client_send query;
    server();
    client_recv query;
    ignore (debug_print_string "\n\n")

val run : unit
let run = test ()
(* check_marker *)

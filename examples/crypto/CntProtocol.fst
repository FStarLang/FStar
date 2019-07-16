(* Copyright (c) Microsoft Corporation.  All rights reserved.  *)

module CntProtocol

#set-options "--max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1"
open FStar.All
open FStar.Set
open FStar.String
open FStar.IO
open FStar.Ref

let init_print = print_string "\ninitializing...\n\n"

open FStar.Seq
open Platform.Bytes
open SHA1
open CntFormat
open MAC

module Bytes = Platform.Bytes

let max x y = if x > y then x else y

(* Events for proving injective agreement *)
type event =
  | Recv : m:uint32 -> c:uint16 -> event

val log_prot: ref (list event)
let log_prot = ST.alloc []

val client_cnt: ref uint16
let client_cnt = lemma_repr_bytes_values 1; ST.alloc 1

val server_cnt: ref uint16
let server_cnt = lemma_repr_bytes_values 0; ST.alloc 0

val server_max: l:list event -> Tot (c:uint16)
let rec server_max l =
  match l with
  | [] -> lemma_repr_bytes_values 0; 0
  | Recv _ c :: l' -> max c (server_max l')

val max_list: s:uint32 -> c:uint16 -> l:list event ->
  Lemma(if c > server_max l then
	  server_max (Recv s c :: l) > server_max l
	else server_max (Recv s c :: l) = server_max l)
let max_list s c l = ()

val max_lemma: s:uint32 -> c:uint16 -> (l:list event{c > server_max l}) ->
  Lemma(forall e . List.Tot.mem e l ==> e <> (Recv s c))
let rec max_lemma s c l =
  match l with
  | [] -> ()
  | Recv s' c' :: l' ->
     max_list s' c' l';
     max_lemma s c l'

let invariant h =
  server_max (Heap.sel h log_prot) = Heap.sel h server_cnt  /\
    Heap.contains h server_cnt /\ Heap.contains h client_cnt /\
      Heap.contains h log_prot /\ (addr_of server_cnt <> addr_of client_cnt)

let fresh_cnt x =
  let y = !server_cnt in
  (y < x)

(*
 * AR: 07/11: since this function has a non-trivial precondition,
 *            adding a spec for it, cf. #1055
 *)
let next_cnt ()
  : ST uint16
    (requires fun h ->
      Bytes.repr_bytes (sel h client_cnt + 1) <= 2)
    (ensures fun h0 r h1 ->
      r == sel h0 client_cnt /\
      modifies !{client_cnt} h0 h1 /\
      sel h1 client_cnt == sel h0 client_cnt + 1)
  = let c  = !client_cnt in
    client_cnt := c+1;
    c

(*
 * AR: 07/11: adding the annotation to ensure a trivial precondition
 *)
let update_cnt (x:uint16) =
  let y = !server_cnt in
  server_cnt := max x y

let log_event e =
  let l = !log_prot in
  log_prot := e::l


val log_and_update: s: uint32 -> c: uint16 -> ST (unit)
    (requires (fun h -> invariant h /\
                        (forall e . List.Tot.mem e (sel h log_prot) ==> e <> (Recv s c)) /\
                        (c > server_max (sel h log_prot))))
    (ensures (fun h x h' -> invariant h' /\ c = sel h' server_cnt /\
                         (sel h' log_prot = Recv s c::sel h log_prot) /\
                         (modifies !{log_prot, server_cnt} h h')))
let log_and_update s c =
  log_event (Recv s c);
  update_cnt c


(* some basic, untrusted network controlled by the adversary *)

val msg_buffer: ref message
let msg_buffer = ST.alloc (empty_bytes)

val send: message -> ST unit
		       (requires (fun h -> True))
		       (ensures (fun h x h' -> modifies !{msg_buffer} h h'))
let send m = msg_buffer := m

val recv: unit -> ST message
		    (requires (fun h -> True))
		    (ensures (fun h x h' -> modifies !{msg_buffer} h h'))
let rec recv _ = if length !msg_buffer > 0
                then (
                  let msg = !msg_buffer in
                  msg_buffer := empty_bytes;
                  msg)
                else recv ()

(* two events, recording genuine requests and responses *)

assume type signal : uint32 -> uint16 -> Type

(* the meaning of MACs, as used in RPC *)

type req (msg:message) =
    (exists s c.   msg = CntFormat.signal s c /\ signal s c)

val k: k:key{key_prop k == req}
let k = keygen req

let recall_all () :ST unit (requires (fun h0      -> True))
                           (ensures  (fun h0 _ h1 -> h0 == h1     /\
			              (let open FStar.Heap in
			               h0 `contains` MAC.log    /\
				       h0 `contains` msg_buffer /\
				       h0 `contains` log_prot   /\
				       h0 `contains` server_cnt)))
  = ST.recall (MAC.log);
    ST.recall (msg_buffer);
    ST.recall (log_prot);
    ST.recall (server_cnt)

val client : uint32 -> ST (option string)
 			  (requires (fun h -> invariant h /\
				     repr_bytes ((sel h client_cnt) + 1) <= 2 ))
 			  (ensures (fun h x h' -> invariant h'))
let client (s: uint32) =
  recall_all ();
  let c = next_cnt () in
  assume (signal s c); //a protocol event
  let t = CntFormat.signal s c in
  let m = mac k t in
  send (t @| m);
  None

val server : unit -> ST (option string)
			(requires (fun h -> invariant h))
			(ensures (fun h x h' -> invariant h' /\ modifies !{log_prot, server_cnt, msg_buffer} h h'))
let server () =
  recall_all ();
  let msg = recv () in (
    if length msg = signal_size + macsize then (
      let (t, m) = split msg signal_size  in
      let (s, c) = CntFormat.signal_split t in
        if fresh_cnt c then(
          if verify k t m then (
	    assert(signal s c);
	    None
	  ) else Some "MAC failed"
	) else Some "Counter already used"
    ) else Some "Wrong length")

let main =
  let x = 10 in
  lemma_repr_bytes_values x;
  print_string ("Client sending: 10\n");
  lemma_repr_bytes_values 2;lemma_repr_bytes_values 1;lemma_repr_bytes_values 0;
  log_prot := [];
  server_cnt := 0;
  client_cnt := 1;
  let a = !log_prot in let b = !server_cnt in
  assume(server_max a = b);
  let _ = client x in
  let x = server () in
  begin
    match x with
    | None -> print_string "Success!\n"
    | Some x -> print_string ("Failure : "^x^"\n")
  end

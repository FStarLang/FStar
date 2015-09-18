(*--build-config
    options:--z3timeout 10 --verify_module CntProtocol --admit_fsi FStar.Seq --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --admit_fsi FStar.IO;
    variables:CONTRIB=../../contrib;
    other-files:
            ext.fst classical.fst
            set.fsi set.fst
            heap.fst st.fst all.fst
            string.fst list.fst
            seq.fsi seqproperties.fst
            io.fsti
            $CONTRIB/Platform/fst/Bytes.fst
            $CONTRIB/CoreCrypto/fst/CoreCrypto.fst
            cnt-format.fst
            sha1.fst
            mac.fst
  --*)


(* Copyright (c) Microsoft Corporation.  All rights reserved.  *)

module CntProtocol

open FStar.All
open FStar.Set
open FStar.String
open FStar.IO
open FStar.Heap


let init_print = print_string "\ninitializing...\n\n"

open FStar.Seq
open FStar.SeqProperties
open Platform.Bytes
open SHA1
open CntFormat
open MAC

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
  Lemma(forall e . List.mem e l ==> e <> (Recv s c))
let rec max_lemma s c l =
  match l with
  | [] -> ()
  | Recv s' c' :: l' ->
     max_list s' c' l';
     max_lemma s c l'

logic type Invariant h =
  server_max (Heap.sel h log_prot) = Heap.sel h server_cnt &&
    Heap.contains h server_cnt && Heap.contains h client_cnt &&
      Heap.contains h log_prot && server_cnt <> client_cnt

let fresh_cnt x =
  let y = !server_cnt in
  (y < x)

let next_cnt () =
  let c  = !client_cnt in
  client_cnt := c+1;
  c

let update_cnt x =
  let y = !server_cnt in
  server_cnt := max x y

let log_event e =
  let l = !log_prot in
  log_prot := e::l

val server_refs: unit -> GTot (set aref)
let server_refs _ = (Set.union (Set.singleton (Ref log_prot))
			       (Set.singleton (Ref server_cnt)))

val log_and_update: s: uint32 -> c: uint16 -> ST (unit)
    (requires (fun h -> Invariant h /\
                        (forall e . List.mem e (sel h log_prot) ==> e <> (Recv s c)) /\
                        (c > server_max (sel h log_prot))))
    (ensures (fun h x h' -> Invariant h' /\ c = sel h' server_cnt /\
                            (sel h' log_prot = Recv s c::sel h log_prot)
                            /\ modifies (server_refs ()) h h'))
let log_and_update s c =
  log_event (Recv s c);
  update_cnt c

(* some basic, untrusted network controlled by the adversary *)

assume val send: message -> ST unit
			       (requires (fun h -> True))
			       (ensures (fun h x h' -> modifies !{} h h'))

assume val recv: unit -> ST message
			    (requires (fun h -> True))
			    (ensures (fun h x h' -> modifies !{} h h'))

(* two events, recording genuine requests and responses *)

logic type Signal : uint32 -> uint16 -> Type

(* the meaning of MACs, as used in RPC *)

opaque logic type req (msg:message) =
    (exists s c.   msg = CntFormat.signal s c /\ Signal s c)

let k = keygen req

val client : uint32 -> ST (option string)
 			  (requires (fun h -> Invariant h /\ repr_bytes ((sel h client_cnt) + 1) < 2 ))
 			  (ensures (fun h x h' -> Invariant h'))
let client (s: uint32) =
  let c = next_cnt () in
  admitP (Signal s c);
  assert(Signal s c);
  let t = CntFormat.signal s c in
  let m = mac k t in
  send (append t m);
  None

val server : unit -> ST (option string)
			(requires (fun h -> Invariant h /\
                                   sel h server_cnt <> sel h client_cnt))
			(ensures (fun h x h' -> Invariant h' /\ modifies (server_refs ()) h h'))
let server () =
  let msg = recv () in (
    if length msg <> signal_size + macsize then Some "Wrong length"
    else
      let (t, m) = split msg signal_size  in
      match signal_split t with
      | Some (s, c) ->
        if fresh_cnt c then
          if verify k t m then (
	          assert(Signal s c);
	          max_lemma s c !log_prot;
	          log_and_update s c;
            None
	        ) else Some "MAC failed"
	      else Some "Counter already used"
      | None -> Some "Bad tag" )

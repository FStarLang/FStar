(*--build-config
    options:--z3timeout 10 --verify_module BloomProtocol --admit_fsi FStar.Seq --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --admit_fsi FStar.IO;
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
            bloom-format.fst
            bloom.fst sha1.fst mac.fst
  --*)


(* Copyright (c) Microsoft Corporation.  All rights reserved.  *)

module BloomProtocol

open FStar.All
open FStar.String
open FStar.IO
open FStar.Heap


let init_print = print_string "\ninitializing...\n\n"

open Platform.Bytes
open FStar.Seq
open FStar.SeqProperties
open CoreCrypto
open Format
open MAC
open SHA1
open Bloom

let max x y = if x > y then x else y

(* Events for proving injective agreement *)
type event =
  | Recv : m:uint32 -> c:uint16 -> event

val log_prot: ref (list event)
let log_prot = ST.alloc []

let filter_size = 32
let filter_keys = 3
let filter_hash = MD5

let bloom_create  = Bloom.create filter_size
let bloom_add     = Bloom.add    filter_size (CoreCrypto.hash filter_hash) filter_keys
let bloom_check   = Bloom.check  filter_size (CoreCrypto.hash filter_hash) filter_keys

val server_filter: ref (bloom filter_size)
let server_filter = ST.alloc (bloom_create)

let all_neq e l = List.for_allT (fun e' -> e' <> e) l

let invariant h =
  Heap.contains h server_filter

let log_event e =
  let l = !log_prot in
  log_prot := e::l

let server_refs = (Set.union (Set.singleton (Ref log_prot))
    			       (Set.singleton (Ref server_filter)))

val bloom_lemma: s:uint32 -> c:uint16 ->
		 bl:bloom filter_size{not (bloom_check (uint16_to_bytes c) bl)} ->
		 l:list event{forall s' c' . List.mem (Recv s' c') l ==> bloom_check (uint16_to_bytes c) bl} ->
		 Lemma (all_neq (Recv s c) l)
let rec bloom_lemma s c bl l =
  match l with
  | [] -> ()
  | Recv s' c' :: l' ->
    bloom_lemma s c bl l'

(* some basic, untrusted network controlled by the adversary *)

assume val send: message -> ST unit
			       (requires (fun h -> True))
			       (ensures (fun h x h' -> modifies !{} h h'))

assume val recv: unit -> ST message
			    (requires (fun h -> True))
			    (ensures (fun h x h' -> modifies !{} h h'))

(* the meaning of MACs, as used in RPC *)

logic type Signal : uint32 -> uint16 -> Type
opaque logic type req (msg:message) =
    (exists s c.   msg = Format.signal s c /\ Signal s c)

let k = keygen req

let client (s: uint32) =
  let c = bytes_to_uint16 (sample 2) in
  admitP (Signal s c);
  let t = Format.signal s c in
  let m = mac k t in
  send (append t m);
  None

val log_and_update: s: uint32 -> c: uint16 -> ST (unit)
    (requires (fun h -> invariant h /\ (all_neq (Recv s c) (sel h log_prot))))
    (ensures (fun h x h' -> invariant h' /\ (bloom_check (uint16_to_bytes c) (sel h' server_filter)) &&
                            (sel h' log_prot = Recv s c::sel h log_prot)
                            /\ modifies server_refs h h'))
let log_and_update s c =
  log_event (Recv s c);
  let bl = !server_filter in
  server_filter := bloom_add (uint16_to_bytes c) bl

let fresh_nonce c =
  not (bloom_check (uint16_to_bytes c) (!server_filter))

let server () =
  let msg = recv () in (
    if length msg <> signal_size + macsize then Some "Wrong length"
    else
      let (t, m) = split msg signal_size  in
      match signal_split t with
      | Some (s, c) ->
        if fresh_nonce c then
          if verify k t m then (
	          assert(Signal s c);
	          log_and_update s c;
            None
	  ) else Some "MAC failed"
	else Some "Counter already used"
      | None -> Some "Bad tag" )


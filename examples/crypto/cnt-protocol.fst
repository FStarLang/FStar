(*--build-config
    options:--z3timeout 10 --prims ../../lib/prims.fst --verify_module CntProtocol --admit_fsi Seq --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1;
    variables:LIB=../../lib;
    other-files:$LIB/string.fst $LIB/list.fst
            $LIB/ext.fst $LIB/classical.fst
            $LIB/set.fsi $LIB/set.fst
            $LIB/heap.fst $LIB/st.fst
            $LIB/seq.fsi $LIB/seqproperties.fst cnt-format.fst cnt-mac.fst
  --*)

module CntProtocol
open Seq
open SeqProperties
open Format
open MAC
open ST
open ML
open Heap

let max x y = if x > y then x else y

(* Events for proving injective agreement *)
type event =
  | Recv : m:uint32 -> c:uint16 -> event

val log_prot: ref (list event)
let log_prot = ST.alloc []

val client_cnt: ref uint16
let client_cnt = ST.alloc 1

val server_cnt: ref uint16
let server_cnt = ST.alloc 0

val server_max: l:list event -> Tot (c:uint16)
let rec server_max l =
  match l with
  | [] -> 0
  | Recv _ c :: l' -> max c (server_max l')

let all_neq e l = List.for_allT (fun e' -> e' <> e) l

val max_list: s:uint32 -> c:uint16 -> l:list event ->
  Lemma(if c > server_max l then
	  server_max (Recv s c :: l) > server_max l
	else server_max (Recv s c :: l) = server_max l)
let max_list s c l = ()

val max_lemma: s:uint32 -> c:uint16 -> (l:list event{c > server_max l}) ->
  Lemma(all_neq (Recv s c) l)
let rec max_lemma s c l =
  match l with
  | [] -> ()
  | Recv s' c' :: l' ->
     max_list s' c' l';
     max_lemma s c l'

let invariant h =
  server_max (sel h log_prot) = sel h server_cnt &&
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

let server_refs = (Set.union (Set.singleton (Ref log_prot))
    			       (Set.singleton (Ref server_cnt)))

val log_and_update: s: uint32 -> c: uint16 -> ST (unit)
    (requires (fun h -> invariant h /\
                        (all_neq (Recv s c) (sel h log_prot)) /\
                        (c > server_max (sel h log_prot))))
    (ensures (fun h x h' -> invariant h' /\ c = sel h' server_cnt /\
                            (sel h' log_prot = Recv s c::sel h log_prot)
                            /\ modifies server_refs h h'))
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
    (exists s c.   msg = Format.signal s c /\ Signal s c)

let k = keygen req

val client : uint32 -> ST (option string)
 			  (requires (fun h -> invariant h /\ sel h client_cnt < uint16_max ))
 			  (ensures (fun h x h' -> invariant h'))
let client (s: uint32) =
  let c = next_cnt () in
  admitP (Signal s c);
  let t = Format.signal s c in
  let m = mac k t in
  send (append t m);
  None

val server : unit -> ST (option string)
			(requires (fun h -> invariant h /\
                                   sel h server_cnt <> sel h client_cnt))
			(ensures (fun h x h' -> invariant h' /\ modifies server_refs h h'))
let server () =
  let msg = recv () in (
    if length msg <> signal_size + macsize then Some "Wrong length"
    else
      let (t, m) = split msg signal_size  in
      match signal_split t with
      | Some (s, c) ->
        if fresh_cnt c then (
          if verify k t m then (
	    assert(Signal s c);
	    max_lemma s c !log_prot;
	    log_and_update s c;
            None
	  ) else Some "MAC failed"
	) else Some "Counter already used"
      | None -> Some "Bad tag" )

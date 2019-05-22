module FStar.ReflexiveTransitiveClosure.Test

open FStar.ReflexiveTransitiveClosure

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

assume val handshake_message : Type

assume val is_client_hello (hs:handshake_message) : Type0

assume val is_server_hello (hs:handshake_message) : Type0

let hs_ch = m:handshake_message{is_client_hello m}

let hs_sh = m:handshake_message{is_server_hello m}

let offer = hs_ch 

type retry = hs_ch & hs_sh

let bounded_list 'a n = l:list 'a{List.Tot.length l < n}

assume val max_transcript_size : nat

noeq
type transcript_t =
  | Start:
      retried:option retry ->
      transcript_t

  | Hello:
      retried:option retry ->
      ch:hs_ch ->
      transcript_t

  | Transcript12:
      ch:hs_ch ->
      sh:hs_sh ->
      rest:bounded_list handshake_message max_transcript_size ->
      transcript_t

  | Transcript13:
      retried:option retry ->
      ch:hs_ch ->
      sh:hs_sh ->
      rest:bounded_list handshake_message max_transcript_size ->
      transcript_t

let transcript_size (t:transcript_t) =
    match t with
    | Start _
    | Hello _ _ -> 0
    | Transcript12 _ _ rest -> List.Tot.length rest
    | Transcript13 _ _ _ rest -> List.Tot.length rest

let trans (n:nat) = tr:transcript_t { transcript_size tr <= n }

assume val mode : Type

noeq
type client_state =
  | C_init : client_state
  
  | C_truncated_ClientHello:
    transcript: Ghost.erased (trans 0) -> 
    offer: offer{ Ghost.reveal transcript == Hello None offer } -> 
    client_state
    
  | C_wait_ServerHello: 
    transcript: Ghost.erased (trans 0) -> 
    offer: offer{ Ghost.reveal transcript == Hello None offer } -> 
    client_state
    
  | C13_wait_Finished1: 
    transcript: Ghost.erased (trans 1) ->
    mode: mode {exists offer sh. Ghost.reveal transcript == Transcript13 None offer sh [] } ->
    client_state 

/// We define an update condition on the state that encodes the state
/// machine and ensures stability on selected properties of
/// interest. For example, the transcript is monotonic; and
/// Negotiation's offer and mode are SSA.

assume val transition_hsm: transcript_t -> handshake_message -> option transcript_t

assume val mode_offer : mode -> offer

let step (st0 st1: client_state) = 
  match st0, st1 with 
  | C_init,
    C_truncated_ClientHello transcript0 offer0 -> True

  | C_truncated_ClientHello transcript0 offer0,
    C_wait_ServerHello      transcript1 offer1 ->
    let transcript0 = Ghost.reveal transcript0 in 
    let transcript1 = Ghost.reveal transcript1 in 
    exists binders. Some transcript1 == transition_hsm transcript0 binders
    // /\ offer1 == transcript_offer transcript1 

  | C_wait_ServerHello transcript0 offer0,
    C13_wait_Finished1 transcript1 mode0 ->
    let transcript0 = Ghost.reveal transcript0 in 
    let transcript1 = Ghost.reveal transcript1 in
    offer0 == mode_offer mode0 /\
    (exists sh. Some transcript1 == transition_hsm transcript0 sh )

  | _, _ -> False 

/// Sample lemma: the offer is SSA

let st_offer (st0: client_state) : option offer = 
  match st0 with 
  | C_wait_ServerHello transcript0 offer0 -> Some offer0 
  | C13_wait_Finished1 transcript0 mode0 -> Some (mode_offer mode0)
  | _ -> None 

val m_offer (st0 st1: client_state):
  Lemma (requires
    (let o0 = st_offer st0 in
     let o1 = st_offer st1 in
     step st0 st1 /\ Some? o0))
    (ensures 
      (let o0 = st_offer st0 in
       let o1 = st_offer st1 in
       o1 == o0))
let m_offer st0 st1 = ()

let mrel = reflexive_transitive_closure step

/// Main type for the connection handshake
noeq abstract type t = | C_State: HST.mreference client_state mrel -> t 

/// Testing monotonicity

open HST

let p (r:mreference client_state mrel) (o:offer) : mem_predicate = 
  fun h0 -> st_offer (HS.sel h0 r) == Some o 

val witness_offer (st:t) : 
  ST (o: offer { let C_State r = st in token_p r (p r o) } )
    (requires fun h0 -> 
       let C_State r = st in 
       h0 `HS.contains` r /\
       ~(C_init? (HS.sel h0 r)) /\
       ~(C_truncated_ClientHello? (HS.sel h0 r)))
    (ensures fun h0 o h1 -> h0 == h1)
let witness_offer st = 
  let C_State r = st in
  let Some o = st_offer !r in
  stable_on_closure step (fun st -> st_offer st == Some o) m_offer;
  witness_p r (p r o);
  o

(*--build-config
options:--fstar_home ../../../FStar --use_hints --include ../../../FStar/ulib/ --include ../../../FStar/ulib/heap;
--*)
module Ariadne 

/// We model the Ariadne protocol for state continuity.
/// https://www.usenix.org/system/files/conference/usenixsecurity16/sec16_paper_strackx.pdf
///
/// The protocol ensures that, as the SGX enclaves gets stopped or
/// its machine crashes, it can be reliably resumed in its last saved
/// state. The protocol relies on
/// - a trusted monotonic counter (implemented in hardware, intuitively expensive to increment)
/// - a trusted fixed key (also implemented in hardware, used for authenticated encryption)
/// - an untrusted but reliable store on the host, to save encrypted counters & states

type index = nat 
type volatile = string // the type of the enclave state; reset on crash.

type state = index * volatile // the type of records protected by authenticated encryption
type sealed = Set.set state // the set of all records encrypted so far (ie. replayable records)
let append (log:sealed) x = Set.union log (Set.singleton x)

/// For the proof, we define a small state machine and its transitions
/// when sealing and incrementing
let ok c x (log:sealed) = // normal state: x will be used on recovery
  forall n z. (Set.mem (n,z) log ==> n <= c /\ (n = c ==> z = x))

let writing c x0 x1 (log:sealed) = // transient state between sealing x1 and incrementing c
  forall n z. (Set.mem (n,z) log  ==> n <= c+1 /\ (n = c ==> z = x0 \/ z = x1) /\ (n = c+1 ==> z = x1))

let crash c x0 x1 (log:sealed) = // `worst' transient state (reachable after crashes while recovering)
  forall n z. (Set.mem (n,z) log ==> n <= c+1 /\ (n >= c ==> z = x0 \/ z = x1))

let recover c x0 x1 (log:sealed) = // transient state after the first recovery increment 
  forall n z. (Set.mem (n,z) log ==> n <= c /\ (n = c ==> z = x0 \/ z = x1))

type case (c:nat) log = 
  | Ok: x0:volatile {ok c x0 log} -> case c log
  | Writing: x0:volatile -> x1:volatile {writing c x0 x1 log} -> case c log
  | Crash: x0:volatile -> x1:volatile {crash c x0 x1 log} -> case c log
  | Recover: x0:volatile -> x1:volatile {recover c x0 x1 log} -> case c log
let case_seal case0 w = 
  match case0 with 
  | Ok v -> Writing v w 
  | Recover v0 v1 -> if v0 = w then Writing v1 w else Writing v0 w
  | Writing v0 v1 | Crash v0 v1 -> Crash v0 v1
let case_incr case0 = 
  match case0 with 
  | Writing _ w -> Ok w 
  | Crash v0 v1 -> Recover v0 v1 

/// For simplicity, we bundle the whole state, but we could also have
/// a region with a counter and an instance of AEAD instead of log0
noeq type counter = | Counter: 
  c: index -> // counter (monotonic)
  log: sealed -> // everything encrypted so far (ghost, monotonic)
  case c log -> // ghost state; saves quantifiers
  counter 

open FStar.All
open FStar.HyperStack
type enclave = ref counter 
let counter0 v = Counter 0 (Set.singleton #state (0,v)) (Ok v)

// privileged; the host gets the sealed state 
val seal: e:enclave -> w:volatile -> ST unit 
(requires (fun h0 ->
  let Counter c0 log0 case0 = sel h0 e in 
  match case0 with 
  | Ok _ -> True
  | Writing v0 v1 -> w = v1
  | Recover v0 v1 | Crash v0 v1 -> w = v0 || w = v1))
(ensures fun h0 _ h1 -> 
  let Counter c0 log0 case0 = sel h0 e in 
  sel h1 e == Counter c0 (append log0 (c0+1,w)) (case_seal case0 w))

let seal e w = 
  recall e; 
  let Counter c0 log0 case0 = !e in 
  e := Counter c0 (append log0 (c0+1,w)) (case_seal case0 w)

// privileged, fallible
val incr: e:enclave -> ST unit 
(requires fun h0 -> 
  let Counter c0 log0 case0 = sel h0 e in 
  Writing? case0 \/ Crash? case0)
(ensures fun h0 _ h1 -> 
  let Counter c0 log0 case0 = sel h0 e in 
  let Counter c1 log1 case1 = sel h1 e in 
  (Writing? case0 \/ Crash? case0) /\
  c1 = c0 + 1 /\ 
  log1 == log0 /\ 
  case1 = case_incr case0)

let incr e = 
  recall e;
  let Counter c log case0 = !e in 
  e := Counter (c + 1) log (case_incr case0)

val store_state: e:enclave -> w:volatile -> ST unit
(requires fun h0 -> let Counter _ _ case0 = sel h0 e in Ok? case0)
(ensures fun h0 _ h1 -> let Counter c1 log1 case1 = sel h1 e in ok c1 w log1 /\ case1 = Ok w)
  
let store_state e w = 
  seal e w; 
  incr e 

// proof-only: we safety strat recovery assuming Crash, whcih cover all other cases
let widen e (w:volatile)  = 
  recall e;
  let Counter c log case = !e in 
  e := Counter c log (match case with 
    | Ok v -> Crash v v
    | Writing v0 v1 | Recover v0 v1 | Crash v0 v1 -> if v1 = w then Crash v0 v1 else Crash v1 v0)

// could be more precise, detailing transitions
val recover_state: e:enclave -> state -> ST (option volatile)
(requires fun h0 -> True)
(ensures fun h0 r h1 -> 
  match r with 
  | None -> h0 == h1
  | Some w1 -> 
    let Counter _ _  case0 = sel h0 e in 
    let Counter c1 log1 case1 = sel h1 e in 
    ok c1 w1 log1  /\ case1 == Ok w1 /\ 
    (match case0 with 
    | Ok w0 -> w1 = w0
    | Writing v0 v0'  | Recover v0 v0' | Crash v0 v0' -> w1 = v0 \/ w1 = v0' ))
  
let recover_state e (n,w) = 
  recall e;
  let Counter c log case0 = !e in 
  if n = c && Set.mem (n,w) log // authenticated decryption
  then ( 
    widen e w; // let Counter c log case = !e in (match case with | Crash v0 v1 -> assert(v1 = w));
    seal e w; // let Counter c log case = !e in (match case with | Crash v0 v1 -> assert(v1 = w));
    incr e; // let Counter c log case = !e in (match case with | Recover v0 v1 -> assert(v1 = w));
    seal e w; // let Counter c log case = !e in (match case with | Writing v0 v1 -> assert(v1 = w));
    incr e; // let Counter c log case = !e in (match case with | Ok v1 -> assert(v1 = w)); 
    Some w)
  else None


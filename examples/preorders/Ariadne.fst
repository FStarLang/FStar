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

open FStar.ST 
open FStar.All
open FStar.Heap
open FStar.MRef

type index = nat // counter values (no overflow detection yet)
type volatile = string // the type of the enclave state; reset on crash.

type record = index * volatile // the type of records protected by authenticated encryption
type sealed = Set.set record // the set of all records encrypted so far (ie. replayable records)
let append (log:sealed) x = Set.union log (Set.singleton x)

/// For the proof, we define a small state machine and its transitions
/// when sealing and incrementing.

type case = 
  | Ok: saved: volatile -> case
  | Recover: read: volatile -> other: volatile -> case
  | Writing: latest: volatile -> prior: volatile -> case
  | Crash: read: volatile -> other: volatile -> case 
type ic = index * case

/// A monotonic over-approximation of the encrypted records the host may have
val sealable: ic -> record -> Type0
let sealable (n,c) s = 
  let m,u = s in 
  (m < n) \/
  (m = n /\ (match c with 
  | Ok v -> u=v
  | Recover w v 
  | Writing w v
  | Crash w v -> u=w \/ u=v)) \/
  (m = n+1 /\ (match c with 
  | Ok _ | Recover _ _ -> False
  | Writing v _ -> u=v
  | Crash v w -> u=v \/ u=w))
let pre (s0 s1: ic) =  forall x. sealable s0 x ==> sealable s1 x
let _ = assert (monotonic ic pre)

/// For simplicity, we bundle the whole state, but we could also have
/// a region with a counter and an instance of AEAD instead of log
noeq type counter = | Counter: 
  n: index -> // counter (monotonic)
  c: case -> // ghost state; saves quantifiers
  log: Set.set record {forall s. Set.mem s log ==> sealable (n,c) s} -> 
  // everything encrypted so far (ghost, monotonic); could be stored elsewhere
  counter 

let rel (Counter n0 c0 log0) (Counter n1 c1 log1) = 
  pre (n0,c0) (n1,c1) /\ Set.subset log0 log1

type enclave = mref counter rel
let counter0 v = Counter 0 (Ok v) (Set.singleton (0,v))
val create: v: volatile -> ST enclave
  (requires fun h0 -> True)
  (ensures fun h0 e h1 -> sel h1 e == counter0 v)
let create v = 
  alloc (counter0 v)

// privileged code calling back into fallible host code: this may
// fail, in which case we still conservatively assume the host gets
// the sealed record (although we can't rely on it for recovery)

let pre0 c w = 
  match c with 
  | Ok u -> True
  | Recover u v
  | Writing u v 
  | Crash u v -> w==u \/ w==v
let step0 c w = 
  match c with 
  | Ok u -> Writing w u
  | Recover u v -> if w=u then Writing u v else Crash w u
  | Writing u v
  | Crash u v -> if w=u then Crash w v else Crash w u
val seal: e:enclave -> w:volatile -> All unit 
(requires fun h0 -> pre0 (sel h0 e).c w)
(ensures fun h0 r h1 -> 
  let Counter n c0 log0 = sel h0 e in 
  pre0 c0 w /\ (
  let c1 = step0 c0 w in
  let log1 = append log0 (n+1,w) in
  sel h1 e == Counter n c1 log1))

let seal e w = 
  let Counter n c0 log0 = read e in
  let c1 = step0 c0 w in
  let log1 = append log0 (n+1,w) in 
  write e (Counter n c1 log1)

/// incrementing the counter is privileged code;
/// it may fail before or after incrementing c
let pre1 c = Writing? c \/ Crash? c
val step1: c:case {pre1 c} -> case
let step1 = function
  | Writing w v -> Ok w
  | Crash v0 v1 -> Recover v0 v1

val incr: e:enclave -> w:volatile -> All unit 
(requires fun h0 -> pre1 (sel h0 e).c)
(ensures fun h0 r h1 -> 
  let v0 = sel h0 e in 
  let Counter n0 c0 log = v0 in 
  pre1 c0 /\ (
  let c1 = step1 c0 in 
  let v1 = Counter (n0+1) c1 log in 
  match r with 
  | V _ ->  sel h1 e ==  v1
  | _ -> sel h1 e == v0 \/ sel h1 e == v1 ))

// sample implementation, with sample failure
let incr e w = 
  let x = read e in
  let Counter n0 c0 log = x in 
  if n0 = 3 then failwith "crash" else // else is required!?
  write e (Counter (n0+1) (step1 c0) log)

/// storing a checkpoint requires a clean state 
val store_state: e:enclave -> w:volatile -> All unit
(requires fun h0 -> Ok? (sel h0 e).c)
(ensures fun h0 r h1 -> 
  let Counter _ c1 _ = sel h1 e in 
  V? r ==> c1 = Ok w)
  
let store_state e w = 
  seal e w; 
  incr e w

/// recovery does not need *any* precondition, and leads to an Ok
/// state (unless it crashes). We could be more precise, e.g. we never
/// get None on honest inputs.
val recover_state: e:enclave -> s:record -> All (option volatile)
(requires fun h0 -> True)
(ensures fun h0 r h1 -> 
  let Counter _ c0 _ = sel h0 e in 
  let Counter _ c1 _ = sel h1 e in 
  match r with 
  | V None -> h0 == h1
  | V (Some w1) -> 
    c1 == Ok w1 /\ 
    (match c0 with 
    | Ok w0 -> w1 = w0
    | Writing v0 v0'  | Recover v0 v0' | Crash v0 v0' -> w1 = v0 \/ w1 = v0' )
  | _ -> False  // should not be provable?!
  )
  
let recover_state e (m,w) = 
  let Counter n c0 log = read e in 
  if m = n && Set.mem (n,w) log // authenticated decryption
  then ( 
    seal e w;
    incr e w;
    seal e w;
    incr e w;
    Some w)
  else None

type whatever 'a = 'a -> All unit (requires fun h0 -> True) (ensures fun h0 _ h1 -> True)
val example: whatever (whatever enclave)
let example attack = 
  let e = create "hello" in
  store_state e "world";
  attack e;
  match recover_state e (1,"world") with 
  | Some _ -> store_state e "!\n"
  | _ -> ()

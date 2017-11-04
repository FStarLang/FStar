 module Ariadne

// CF: We model the Ariadne protocol for state continuity.
// https://www.usenix.org/system/files/conference/usenixsecurity16/sec16_paper_strackx.pdf
//
// The protocol ensures that, as the SGX enclave gets stopped or
// its machine crashes, it can be reliably resumed in its last saved
// state. The protocol relies on
// - a trusted monotonic counter (implemented in hardware, intuitively expensive to increment)
// - a trusted fixed key (also implemented in hardware, used for authenticated encryption)
// - an untrusted but reliable store on the host, to save encrypted counters & states

open FStar.Preorder
open FStar.List.Tot

open FStar.All // Compared to the accompanying POPL'18 paper, we use F*'s All effect to 
               // use the combination of state and exceptions (MSTMSTExn in the paper)

open FStar.Heap
open FStar.ST 
open FStar.MRef


type index = nat // counter values (no overflow detection yet)
type state = string // the type of the enclave state; reset on crash.

type record = index * state // the type of records protected by authenticated encryption

// For the proof, we define a small state machine and its transitions
// when sealing and incrementing.

type case = 
  | Ok: saved: state -> case
  | Recover: read: state -> other: state -> case
  | Writing: written: state -> old: state -> case
  | Crash: read: state -> other: state -> case 

type counter =
  | Counter: 
    n: index -> // counter (monotonic)
    c: case -> // ghost state; saves quantifiers
    counter 

// A monotonic over-approximation of the encrypted records the host may have
val saved: counter -> record -> Type0
let saved (Counter n c) s = 
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

let preorder' :preorder counter = fun (x0:counter) (x1:counter) -> forall s. saved x0 s ==> saved x1 s

type ctr = mref counter preorder' 

// An encrypted backup, maintained by the host This is compatible
// with our ideal interface for authenticated encryption.

let saved_backup (c:ctr) (s:record) = fun h -> h `contains` c /\ saved (sel h c) s

type backup (c:ctr) = s:record{witnessed (saved_backup c s)}

let prefix_of (#c:ctr) (l1:list (backup c)) (l2:list (backup c)) =
  l1 == l2 \/ strict_prefix_of l1 l2
  
let backups_pre' (c:ctr) :relation (list (backup c)) = fun l1 l2 -> l1 `prefix_of` l2
let backups_pre (c:ctr) :preorder (list (backup c)) = backups_pre' c

type backups (c:ctr) = mref (list (backup c)) (backups_pre c) // Compared to the general situation described in the
                                                              // POPL'18 paper, for simplicity, here we consider only  
                                                              // trivial backup keys, i.e., key c = backups c. Thus, 
                                                              // we omit the auth_encrypt and auth_decrypt functions
noeq type protected = 
  | Protect: c:ctr -> b:backups c -> protected

val create: v: state -> ST protected
  (requires fun h0 -> True)
  (ensures fun h0 (Protect e b) h1 -> sel h1 e == Counter 0 (Ok v))
let create v = 
  let e = alloc (Counter 0 (Ok v)) in 
  let r = (0,v) in
  witness (saved_backup e r);
  let b = alloc [r] in 
  Protect e b 

// Privileged code calling back into fallible host code: this may
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
  
val save: p:protected -> w:state -> All unit 
(requires fun h0 -> 
  let Protect c b = p in 
  let Counter _ c0 = sel h0 c in 
  pre0 c0 w)
(ensures fun h0 r h1 -> 
  let Protect c b = p in
  let Counter n c0 = sel h0 c in 
  pre0 c0 w /\ (
  let c1 = step0 c0 w in
  sel h1 c == Counter n c1))

let save p w = 
  let Protect c b = p in
  let Counter n c0 = read c in
  let c1 = step0 c0 w in
  write c (Counter n c1); 
  let r = (n+1,w) in 
  witness (saved_backup c r);
  let log0 = read b in 
  write b (r::log0)

// Incrementing the counter is privileged code; it may fail before or after incrementing c
let pre1 c = Writing? c \/ Crash? c
val step1: c:case {pre1 c} -> case
let step1 = function
  | Writing w v -> Ok w
  | Crash v0 v1 -> Recover v0 v1

val incr: c:ctr -> w:state -> All unit 
(requires fun h0 -> 
  let Counter _ c0 = sel h0 c in
  pre1 c0)
(ensures fun h0 r h1 -> 
  let v0 = sel h0 c in 
  let Counter n0 c0  = v0 in 
  pre1 c0 /\ (
  let c1 = step1 c0 in 
  let v1 = Counter (n0+1) c1 in 
  match r with 
  | V _ ->  sel h1 c ==  v1
  | _ -> sel h1 c == v0 \/ sel h1 c == v1 ))

// A sample implementation of incr, with sample failure
let incr c w = 
  let x = read c in
  let Counter n0 c0 = x in 
  if n0 = 3 then failwith "crash" else
  write c (Counter (n0+1) (step1 c0))

// storing a checkpoint requires a clean state 
val store: p:protected -> w:state -> All unit
(requires fun h0 -> 
  let Protect c b = p in 
  let Counter _ c0 = sel h0 c in
  Ok? c0)
(ensures fun h0 r h1 -> 
  let Protect c b = p in
  let Counter _ c1 = sel h1 c in 
  V? r ==> c1 = Ok w)
  
let store p w = 
  let Protect c b = p in 
  save p w; 
  incr c w

// recovery does not need *any* precondition, and leads to an Ok state (unless it crashes)
val recover: p:protected -> last_saved:backup (Protect?.c p) -> All (option state)
(requires fun h0 -> True)
(ensures fun h0 r h1 -> 
  let Protect c b = p in
  let Counter _ c0 = sel h0 c in 
  let Counter _ c1 = sel h1 c in 
  match r with 
  | V None -> h0 == h1
  | V (Some w1) -> (
    c1 == Ok w1 /\ 
    (match c0 with 
    | Ok w0 -> w1 = w0
    | Writing v0 v0'  | Recover v0 v0' | Crash v0 v0' -> w1 = v0 \/ w1 = v0' ))
  | _ -> True
  )

let recover p last_saved = 
  let Protect c b = p in 
  let m, w = last_saved in
  let Counter n c0 = read c in 
  if m = n  // authenticated decryption
  then ( 
    recall (saved_backup c last_saved);
    save p w;
    incr c w;
    save p w;
    incr c w;
    Some w)
  else None

type trivial 'a = 'a -> All unit (requires fun h0 -> True) (ensures fun h0 _ h1 -> True)
val example: trivial (trivial ctr)
let example attack = 
  let p = create "hello" in
  let Protect c b = p in
  store p "world";
  attack c;
  match read b with 
  | r::_ -> 
    (match recover p r with 
    | Some _ -> store p "!\n"
    | _ -> ())
| _ -> ()

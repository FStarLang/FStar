 module Ariadne

/// CF: We model the Ariadne protocol for state continuity.
/// https://www.usenix.org/system/files/conference/usenixsecurity16/sec16_paper_strackx.pdf
///
/// The protocol ensures that, as the SGX enclaves gets stopped or
/// its machine crashes, it can be reliably resumed in its last saved
/// state. The protocol relies on
/// - a trusted monotonic counter (implemented in hardware, intuitively expensive to increment)
/// - a trusted fixed key (also implemented in hardware, used for authenticated encryption)
/// - an untrusted but reliable store on the host, to save encrypted counters & states

open FStar.Preorder
open FStar.List.Tot

open FStar.All

open FStar.Heap
open FStar.ST 
open FStar.MRef


type index = nat // counter values (no overflow detection yet)
type volatile = string // the type of the enclave state; reset on crash.

type record = index * volatile // the type of records protected by authenticated encryption

/// For the proof, we define a small state machine and its transitions
/// when sealing and incrementing.

type case = 
  | Ok: saved: volatile -> case
  | Recover: read: volatile -> other: volatile -> case
  | Writing: latest: volatile -> prior: volatile -> case
  | Crash: read: volatile -> other: volatile -> case 

type counter =
  | Counter: 
    n: index -> // counter (monotonic)
    c: case -> // ghost state; saves quantifiers
    counter 

/// A monotonic over-approximation of the encrypted records the host may have
val sealable: counter -> record -> Type0
let sealable (Counter n c) s = 
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

let pre :preorder counter = fun (x0:counter) (x1:counter) -> forall s. sealable x0 s ==> sealable x1 s

type enclave = mref counter pre 

/// An encrypted backup, maintained by the host This is compatible
/// with our ideal interface for authenticated encryption.

let sealable_pred (e:enclave) (s:record) = fun h -> h `contains` e /\ sealable (sel h e) s
type entry (e:enclave) = s:record{witnessed (sealable_pred e s)}

let prefix_of (#e:enclave) (l1:list (entry e)) (l2:list (entry e)) =
  l1 == l2 \/ strict_prefix_of l1 l2
let backup_pre' (e:enclave) :relation (list (entry e)) = fun l1 l2 -> l1 `prefix_of` l2
let backup_pre (e:enclave) :preorder (list (entry e)) = backup_pre' e

type backup (e:enclave) = mref (list (entry e)) (backup_pre e) // could be finer

val create: v: volatile -> ST (e:enclave & backup e)
  (requires fun h0 -> True)
  (ensures fun h0 (|e, b|) h1 -> sel h1 e == Counter 0 (Ok v))
let create v = 
  let e = alloc (Counter 0 (Ok v)) in 
  let r = (0,v) in
  witness (sealable_pred e r);
  let b = alloc [r] in 
  (|e,  b |) 

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
val seal: e:enclave -> b:backup e -> w:volatile -> All unit 
(requires fun h0 -> pre0 (sel h0 e).c w)
(ensures fun h0 r h1 -> 
  let Counter n c0 = sel h0 e in 
  pre0 c0 w /\ (
  let c1 = step0 c0 w in
  //let log1 = append log0 (n+1,w) in
  sel h1 e == Counter n c1))

let seal e b w = 
  let Counter n c0 = read e in
  let c1 = step0 c0 w in
  write e (Counter n c1); 
  let r = (n+1,w) in 
  witness (sealable_pred e r);
  let log0 = read b in 
  write b (r::log0)

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
  let Counter n0 c0  = v0 in 
  pre1 c0 /\ (
  let c1 = step1 c0 in 
  let v1 = Counter (n0+1) c1 in 
  match r with 
  | V _ ->  sel h1 e ==  v1
  | _ -> sel h1 e == v0 \/ sel h1 e == v1 ))

// sample implementation, with sample failure
let incr e w = 
  let x = read e in
  let Counter n0 c0 = x in 
  if n0 = 3 then failwith "crash" else // else is required!?
  write e (Counter (n0+1) (step1 c0))

/// storing a checkpoint requires a clean state 
val store_state: e:enclave -> b:backup e -> w:volatile -> All unit
(requires fun h0 -> Ok? (sel h0 e).c)
(ensures fun h0 r h1 -> 
  let Counter _ c1 = sel h1 e in 
  V? r ==> c1 = Ok w)
  
let store_state e b w = 
  seal e b w; 
  incr e w

/// recovery does not need *any* precondition, and leads to an Ok
/// state (unless it crashes). We could be more precise, e.g. we never
/// get None on honest inputs.
val recover_state: e:enclave -> b:backup e -> r:entry e -> All (option volatile)
(requires fun h0 -> True)
(ensures fun h0 r h1 -> 
  let Counter _ c0 = sel h0 e in 
  let Counter _ c1 = sel h1 e in 
  match r with 
  | V None -> h0 == h1
  | V (Some w1) -> (
    c1 == Ok w1 /\ 
    (match c0 with 
    | Ok w0 -> w1 = w0
    | Writing v0 v0'  | Recover v0 v0' | Crash v0 v0' -> w1 = v0 \/ w1 = v0' ))
  | _ -> True  // should not be provable?! AR: changed it to True from False, after fixing all_wp in Pervasives
  )
 
let recover_state e b r = 
  let m, w = r in
  let Counter n c0 = read e in 
  if m = n  // authenticated decryption
  then ( 
    recall (sealable_pred e r);
    seal e b w;
    incr e w;
    seal e b w;
    incr e w;
    Some w)
  else None

type whatever 'a = 'a -> All unit (requires fun h0 -> True) (ensures fun h0 _ h1 -> True)
val example: whatever (whatever enclave)
let example attack = 
  let (|e, b|) = create "hello" in
  store_state e b "world";
  attack e;
  match read b with 
  | r::_ -> 
    (match recover_state e b r with 
    | Some _ -> store_state e b "!\n"
    | _ -> ())
| _ -> ()

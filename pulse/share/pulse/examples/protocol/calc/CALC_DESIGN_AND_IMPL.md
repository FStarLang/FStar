# Layered Log Specification: A Pattern for Verifying Stateful Protocols

**A Reusable Framework for End-to-End Functional Correctness in F*/Pulse**

---

This is the canonical design and implementation document for `calc_sample/`.
Older root-level calc status notes have been folded into this file. Use it as
the reference for the `process_request`/layered-log proof pattern that
`TLS_DESIGN_AND_IMPL.md` applies to the TLS client.

## Introduction

This document describes the **layered log specification pattern** used to achieve complete functional correctness proofs for the calc_sample verified calculator server (2183 lines, 0 admits, ~12s verification). The pattern provides end-to-end correspondence between raw bytes, protocol messages, and state transitions for interactive stateful protocols.

**Key insight:** A monotonic ghost log with a multi-layered consistency predicate connects three levels of abstraction:
1. **Wire level** - Raw bytes sent and received
2. **Message level** - Parsed protocol messages  
3. **Semantic level** - Abstract state machine transitions

This framework is directly applicable to TLS 1.3, database protocols, distributed systems, and any stateful protocol requiring wire-to-semantic correspondence proofs.

---

## Table of Contents

1. [Core Concept: Layered Log Specification](#core-concept-layered-log-specification)
2. [Architecture: Four Specification Layers](#architecture-four-specification-layers)
3. [Implementation: Modular Structure](#implementation-modular-structure)
4. [The server_exactly Predicate](#the-server_exactly-predicate)
5. [Proof Engineering Patterns](#proof-engineering-patterns)
6. [Module Reference](#module-reference)

---

## Core Concept: Layered Log Specification

### The Central Idea

Instead of verifying individual operations in isolation, we maintain a **ghost log** that tracks the complete interaction history at three levels simultaneously:

```fstar
type calc_log = {
  // Wire level: raw bytes
  input_bytes:  bytes;   // All bytes received
  output_bytes: bytes;   // All bytes sent
  
  // Message level: parsed protocol structures
  requests:  list request;   // Parsed from input_bytes
  responses: list response;  // Serialized to output_bytes
  
  // Semantic level: abstract state
  current_state: calc_stack;  // Result of executing requests
}
```

The **log_consistent** predicate ensures these three levels stay synchronized:

```fstar
let log_consistent (log: calc_log) : prop =
  // Layer 1→2: Wire bytes parse to messages
  all_parse log.input_bytes /\
  parse_requests log.input_bytes == log.requests /\
  
  // Layer 2→3: Messages execute to state  
  let (state, resps) = run [] log.requests in
  log.current_state == state /\
  log.responses == resps /\
  
  // Layer 2→1: Messages serialize to wire bytes
  serialize_responses log.responses `Seq.equal` log.output_bytes /\
  
  // Wire format invariants
  Seq.length log.input_bytes % 5 == 0 /\
  Seq.length log.output_bytes % 5 == 0
```

### Why This Works

**Monotonicity:** The log only grows (via preorder `log_evolves`). Each operation appends to the log, never modifying history.

**Automatic correspondence:** Every imperative operation that modifies concrete state must also:
1. Append raw bytes to the log
2. Prove the new log remains consistent
3. This transitively proves wire-to-semantic correspondence

**Modular verification:** Each handler proves its local property. The dispatcher composes them via `log_single_step`.

---

## Architecture: Four Specification Layers

### Layer 1: Wire Format (Calc.Wire.fst)

**Purpose:** Define the byte-level protocol without implementation details.

**Key functions:**
```fstar
// Parsing: bytes → messages (pure, spec-level)
val parse_request : bytes{length==5} -> option request

// Serialization: messages → bytes (pure, spec-level)  
val serialize_response : response -> bytes{length==5}

// Big-endian encoding (used in parsing/serialization)
val be_to_n : bytes{length==4} -> int
val n_to_be : int -> bytes{length==4}
```

**Design principle:** Use unbounded types (`int`, `list`, `Seq.seq`) freely. This layer is spec-only, hidden from C extraction.

**Why separate from implementation:** Allows reasoning about wire format properties (parsing injectivity, serialization round-trips) independently of imperative code.

---

### Layer 2: State Machine (Calc.Spec.fst)

**Purpose:** Define the abstract operational semantics without wire format concerns.

**Key function:**
```fstar
val step : calc_stack -> request -> (calc_stack & response)
```

**Critical design choice - Errors as transitions:**
```fstar
let step (stack: calc_stack) (req: request) : (calc_stack & response) =
  match req with
  | Push n -> (n :: stack, Ok)
  | Peek -> 
      (match stack with
       | [] -> (stack, Error)      // Error is a transition!
       | x::_ -> (stack, Result x))
  | Add ->
      (match stack with
       | x::y::rest -> ((x + y) % pow2 32 :: rest, Ok)
       | _ -> (stack, Error))      // Not a precondition violation
  // ...
```

**Why errors as transitions:** 
- Allows ghost log to track ALL operations, including failed ones
- Eliminates need for `step_pre` predicates
- Simplifies proof structure (no partial functions)

**Why modular arithmetic:**
```fstar
(x + y) % pow2 32  // Matches U32.t wrapping semantics
```
Ensures spec matches implementation behavior exactly.

---

### Layer 3: Ghost Log (Calc.Log.fst)

**Purpose:** Bridge wire format, messages, and state machine with correspondence proofs.

**Core type:**
```fstar
type calc_log = {
  input_bytes:  bytes;
  output_bytes: bytes;
  requests:  list request;
  responses: list response;
  current_state: calc_stack;
}
```

**Evolution and consistency:**
```fstar
// Monotonic preorder
val log_evolves : preorder calc_log

// Multi-layer consistency
val log_consistent : calc_log -> prop

// Single-step evolution
val log_single_step : calc_log -> calc_log -> prop
```

**Step functions (one per operation):**
```fstar
val step_log_push : 
  log0:calc_log -> 
  req_bytes:bytes{length==5} -> 
  value:int -> 
  calc_log  // Returns new log

val lemma_step_log_push_consistent :
  log0:calc_log -> req_bytes:bytes{length==5} -> value:int ->
  Lemma (requires log_consistent log0 /\ parse_request req_bytes == Some (Push value))
        (ensures log_consistent (step_log_push log0 req_bytes value))
```

**Pattern:** For each operation type:
1. `step_log_X` - Pure function computing next log
2. `lemma_step_log_X_consistent` - Proves consistency preserved
3. `lemma_step_log_X_evolves` - Proves log_evolves holds

**The all_parse predicate:**
```fstar
let rec all_parse (bs: bytes) : prop =
  if Seq.length bs = 0 then True
  else if Seq.length bs < 5 then False
  else 
    Some? (parse_request (Seq.slice bs 0 5)) /\
    all_parse (Seq.slice bs 5 (Seq.length bs))
```

**Why integrate into log_consistent:** Makes parsing success automatic, not a separate precondition. Enables inductive proofs over message sequences.

---

### Layer 4: Concrete State (Calc.Impl.Types.fst)

**Purpose:** Connect ghost log to imperative heap state.

**Concrete representation:**
```fstar
noeq type server_state = {
  stack: Vec.vec U32.t;        // Heap-allocated stack
  count: Vec.vec SZ.t;         // Single-element vec for count
  log:   R.ref (erased calc_log);  // Ghost log reference
}
```

**The bridge predicate:**
```fstar
val server_exactly : 
  server_state -> 
  erased calc_log -> 
  slprop

let server_exactly (srv: server_state) (log: erased calc_log) : slprop =
  exists* stack_bytes count_val.
    Vec.pts_to srv.stack stack_bytes **
    Vec.pts_to srv.count count_val **
    R.pts_to srv.log log **
    pure (
      // Concrete ↔ Ghost correspondence
      SZ.v count_val == List.Tot.length (reveal log).requests /\
      
      // Stack contents match ghost state
      (forall (i:nat). i < SZ.v count_val ==>
        U32.v (Seq.index stack_bytes i) == List.Tot.index (reveal log).current_state i) /\
      
      // Ghost log is consistent
      log_consistent (reveal log)
    )
```

**Key properties:**
- `server_exactly` is **unfoldable** (not opaque)
- Contains `log_consistent` - fold automatically maintains consistency
- Explicit correspondence between Vec contents and ghost list

---

## Implementation: Modular Structure

### Component Hierarchy

```
Calc.Server.fst (Dispatcher)
    ├─> Calc.Impl.Push.fst ─┐
    ├─> Calc.Impl.Peek.fst  │
    ├─> Calc.Impl.Add.fst   ├─> All use Calc.Impl.Types
    ├─> Calc.Impl.Sub.fst   │   (server_exactly)
    ├─> Calc.Impl.Mul.fst   │
    └─> Calc.Impl.Div.fst  ─┘
         │
         └─> Calc.Impl.Parser.fst ─> Calc.Wire.Lemmas.fst
                  │
                  └─> Calc.Wire.fst
                       │
                       └─> Calc.Spec.fst
                            │
                            └─> Calc.Log.fst
```

### Parser Layer (Calc.Impl.Parser.fst)

**Purpose:** Imperative byte operations with postconditions relating to spec.

```pulse
fn parse_push_value (buf: Vec.vec U8.t)
  requires Vec.pts_to buf 'bytes ** pure (Seq.length 'bytes == 5)
  returns value: U32.t
  ensures Vec.pts_to buf 'bytes **
          pure (U32.v value == be_to_n (Seq.slice 'bytes 1 5))
{
  let b1 = buf.(1sz);
  let b2 = buf.(2sz);
  let b3 = buf.(3sz);
  let b4 = buf.(4sz);
  
  // Arithmetic lemmas connect U32 ops to spec
  Calc.Wire.Lemmas.lemma_parse_push_value_correct b1 b2 b3 b4 (Seq.slice 'bytes 1 5);
  Calc.Wire.Lemmas.lemma_u32_arithmetic_correspondence ...;
  
  // Compute via U32 arithmetic
  U32.add (U32.add (U32.mul v0 16777216ul) ...) v3
}
```

**Proof strategy:** Call arithmetic correctness lemmas to prove U32 operations match spec's `be_to_n`.

---

### Handler Pattern (e.g., Calc.Impl.Push.fst)

Each handler follows a uniform structure:

**1. Helper for response serialization:**
```pulse
fn write_ok_response (resp_buf: Vec.vec U8.t)
  requires Vec.pts_to resp_buf 'bytes ** pure (Seq.length 'bytes == 5)
  ensures Vec.pts_to resp_buf 'bytes **
          pure (serialize_response Ok `Seq.equal` 'bytes)
{
  resp_buf.(0sz) <- 0uy;  // OK tag
  // ... write zeros for data field
}
```

**2. Main handler proving wire-to-semantic correspondence:**
```pulse
fn process_push
  (srv: server_state)
  (value: U32.t)
  (req_buf resp_buf: Vec.vec U8.t)
  (#log0: erased calc_log)
  (#req_bytes: erased bytes{length==5})
requires
  server_exactly srv log0 **
  Vec.pts_to req_buf req_bytes **
  Vec.pts_to resp_buf 'resp_bytes **
  pure (parse_request req_bytes == Some (Push (U32.v value)))
returns _:unit
ensures exists* resp_bytes1 log1.
  server_exactly srv log1 **
  Vec.pts_to req_buf req_bytes **
  Vec.pts_to resp_buf resp_bytes1 **
  pure (
    // Ghost log evolved correctly
    log_single_step log0 log1 /\
    // Response bytes correct
    serialize_response (snd (step (reveal log0).current_state (Push (U32.v value))))
      `Seq.equal` resp_bytes1
  )
{
  unfold server_exactly;
  with stack_bytes0 count_val0. _;
  
  // Update concrete stack
  let count = Vec.op_Array_Access srv.count 0sz;
  Vec.op_Array_Assignment srv.stack count value;
  Vec.op_Array_Assignment srv.count 0sz (count `SZ.add` 1sz);
  
  // Update ghost log
  let log0' = R.op_Bang srv.log;
  let log1 = CL.step_log_push (reveal log0') req_bytes (U32.v value);
  
  // Prove consistency
  CL.lemma_step_log_push_consistent (reveal log0') req_bytes (U32.v value);
  CL.lemma_step_log_push_evolves (reveal log0') req_bytes (U32.v value);
  
  // Advance ghost log
  R.op_Colon_Equals srv.log (hide log1);
  
  // Write response
  write_ok_response resp_buf;
  
  fold server_exactly;
}
```

**Key steps:**
1. Unfold `server_exactly` to access heap resources
2. Perform concrete imperative operations
3. Compute new ghost log via `step_log_push`
4. Call consistency lemma
5. Update ghost log reference
6. Fold `server_exactly` - this requires proving new log is consistent!

---

### Dispatcher (Calc.Server.fst)

**Purpose:** Parse tag, dispatch to handler, prove `log_single_step`.

```pulse
fn new_server() 
  requires emp
  returns srv: server_state
  ensures exists* log0. server_exactly srv log0 ** 
          pure (reveal log0 == empty_log)
{
  let stack = Vec.alloc 0ul 0sz;
  let count = Vec.alloc 0sz 1sz;
  let log = R.alloc (hide empty_log);
  
  fold (server_exactly {stack; count; log} (hide empty_log));
  {stack; count; log}
}

fn process_request
  (srv: server_state)
  (req_buf resp_buf: Vec.vec U8.t)
  (#log0: erased calc_log)
  (#req_bytes: erased bytes{length==5})
requires
  server_exactly srv log0 **
  Vec.pts_to req_buf req_bytes **
  Vec.pts_to resp_buf 'resp_bytes **
  pure (Some? (parse_request req_bytes))
returns _:unit
ensures exists* resp_bytes1 log1.
  server_exactly srv log1 **
  Vec.pts_to req_buf req_bytes **
  Vec.pts_to resp_buf resp_bytes1 **
  pure (log_single_step log0 log1)  // THE KEY POSTCONDITION
{
  let tag = parse_tag req_buf;
  
  if U8.eq tag 0uy {
    let value = parse_push_value req_buf;
    
    // Call parse_request correspondence lemma
    lemma_be_to_n_equiv (Seq.slice req_bytes 1 5);
    assert (pure (parse_request req_bytes == Some (Push (U32.v value))));
    
    // Dispatch
    Push.process_push srv value req_buf resp_buf;
    
    // Handler postcondition gives us log_single_step!
    with resp_bytes1 log1. _;
    assert (pure (log_single_step log0 log1))
    
  } else if U8.eq tag 1uy {
    Peek.process_peek srv req_buf resp_buf;
    with resp_bytes1 log1. _;
    assert (pure (log_single_step log0 log1))
    
  } // ... other operations
}
```

**Proof structure:**
1. Parse tag to determine operation type
2. Call appropriate handler
3. Handler postcondition provides `log_single_step` witness
4. Existential binding (`with ... . _`) exposes the new log
5. Assert proves the overall postcondition

---

## The server_exactly Predicate

This is the central abstraction connecting all layers.

### Definition (Unfoldable)

```fstar
val server_exactly : server_state -> erased calc_log -> slprop

let server_exactly (srv: server_state) (log: erased calc_log) : slprop =
  exists* stack_bytes count_val.
    Vec.pts_to srv.stack stack_bytes **
    Vec.pts_to srv.count count_val **
    R.pts_to srv.log log **
    pure (
      // Count matches number of requests processed
      SZ.v count_val == List.Tot.length (reveal log).requests /\
      
      // Stack contents = semantic state
      (forall (i:nat). i < SZ.v count_val ==>
        U32.v (Seq.index stack_bytes i) == 
        List.Tot.index (reveal log).current_state i) /\
      
      // Consistency maintained
      log_consistent (reveal log)
    )
```

### Why Unfoldable (Not Opaque)

**Advantages:**
- Fold/unfold in handlers without explicit lemmas
- Automatic propagation of `log_consistent` when folding
- Direct access to heap resources when unfolded

**Alternative (Opaque with lemmas):**
```fstar
val server_exactly : server_state -> erased calc_log -> slprop

// Would require manual lemmas for every operation:
val lemma_unfold_server_exactly : ...
val lemma_fold_server_exactly : ...
val lemma_server_exactly_consistent : ...
```

**Trade-off:** Unfoldable reveals implementation details, but for this internal predicate (not exposed to clients), the simplicity outweighs abstraction benefits.

---

## Proof Engineering Patterns

### Pattern 1: Arithmetic Correctness Lemmas

**Problem:** Prove U32 modular arithmetic matches spec's mathematical arithmetic.

**Solution:** Factor into focused lemmas in Calc.Wire.Lemmas.fst:

```fstar
// Prove no overflow for byte values
val lemma_u32_no_overflow : 
  v0:nat -> v1:nat -> v2:nat -> v3:nat ->
  Lemma (requires v0 < 256 /\ v1 < 256 /\ v2 < 256 /\ v3 < 256)
        (ensures v0 * 16777216 + v1 * 65536 + v2 * 256 + v3 < pow2 32)

// Prove U32 ops match math (given no overflow)
val lemma_u32_arithmetic_correspondence :
  v0:U32.t -> v1:U32.t -> v2:U32.t -> v3:U32.t ->
  Lemma (requires U32.v v0 < 256 /\ U32.v v1 < 256 /\ ...)
        (ensures U32.v (U32.add (U32.mul v0 16777216ul) ...) == 
                 U32.v v0 * 16777216 + ...)
```

**Usage in parser:** Call both lemmas to connect U32 operations to spec.

**Note on "unrefined pattern":** The code uses `be_to_n_unrefined` (taking raw U8.t parameters) instead of `be_to_n` (taking refined bytes{length==4}), but testing shows **refined types work fine in Pulse postconditions**. This is a style choice, not a requirement. Use whichever is clearer.

---

### Pattern 2: all_parse Integration

**Problem:** Lemmas about parsing message sequences need to know all messages parse successfully.

**Wrong approach:**
```fstar
val lemma_parse_append : 
  bs1:bytes -> bs2:bytes ->
  Lemma (requires Some? (parse bs1) /\ Some? (parse bs2))  // Separate precondition
        (ensures ...)
```

**Right approach:** Integrate into consistency predicate:

```fstar
let log_consistent (log: calc_log) : prop =
  all_parse log.input_bytes /\  // Automatic!
  parse_requests log.input_bytes == log.requests /\
  ...
```

**Why better:**
- Handlers prove `log_consistent` automatically via fold
- No need to thread parsing success through calls
- Inductive proofs work cleanly

**Helper lemma:**
```fstar
val lemma_all_parse_append :
  bs:bytes -> msg:bytes{length==5} ->
  Lemma (requires all_parse bs /\ Some? (parse_request msg))
        (ensures all_parse (Seq.append bs msg))
```

---

### Pattern 3: Modular Arithmetic Alignment

**Problem:** Spec must match implementation semantics exactly.

**Wrong:**
```fstar
// Spec uses mathematical addition
let step stack (Add x y) = (x + y) :: rest  // Unbounded!
```

**Right:**
```fstar
// Spec uses modular arithmetic matching U32.t
let step stack (Add x y) = ((x + y) % pow2 32) :: rest
```

**Why:** Ensures spec behavior matches implementation wrapping. Eliminates a class of spec/impl mismatches.

---

### Pattern 4: Proof Ordering in Consistency

**Critical:** The order of conjuncts in `log_consistent` matters for type-checking:

```fstar
let log_consistent (log: calc_log) : prop =
  // FIRST: Establish length refinements
  Seq.length log.input_bytes % 5 == 0 /\
  Seq.length log.output_bytes % 5 == 0 /\
  
  // SECOND: Use refinements in dependent properties
  all_parse log.input_bytes /\  // Needs length % 5 == 0
  
  // THIRD: Use parsing results
  parse_requests log.input_bytes == log.requests /\
  ...
```

**Why:** F* checks refinements left-to-right. Later conjuncts can assume earlier ones hold.

---

### Pattern 5: Existential Witness Binding

**In Pulse, existential witnesses from postconditions must be bound:**

```pulse
handler_call();  // Returns exists* x y. post

// WRONG: Can't directly use x, y

// RIGHT: Bind witnesses
with x y. _;

// NOW: x and y are in scope (as ghost values)
assert (pure (property_of x y));
```

**Critical:** Witnesses from `with` are **ghost** - cannot pass to stateful operations. Read from concrete structures instead.

---

### Pattern 6: Vec vs Array for Heap Allocation

**Problem:** `Array.alloc` extracts to C stack allocation → dangling pointers when struct is returned.

**Solution:** Use `Vec.alloc` for heap allocation:

```pulse
// WRONG: Stack allocation; produces a deprecation warning
let stack = Array.alloc 0ul 0sz;  // C: uint32_t stack[0] on stack
return {stack; ...}                // Dangling pointer!

// RIGHT: Heap allocation  
let stack = Vec.alloc 0ul 0sz;    // C: malloc(...)
return {stack; ...}                // Safe!
```

**Pattern:** Use `Vec` for any data that must persist beyond function scope.

---

### Pattern 7: Use Box instead of Ref for heap-allocated mutable references

```pulse
// WRONG: Stack allocation
let stack = Ref.alloc true;  
return {stack; ...}                // Dangling pointer!

// RIGHT: Heap allocation  
let heap_ref = Box.alloc true;        // C: malloc(...)
return {heap_ref; ...}                // Safe!
```

---

## Client Mirror: A Small Client State Machine

The calculator server above is the small-scale analogue of the TLS **server**.
For symmetry with the TLS **client**, `calc_sample` also includes a small
**client state machine** built with the exact same layered-log technique, but
with the send/receive directions flipped.

Where the server *receives* requests and *sends* responses, the client *sends*
requests and *receives* responses. The client adds a genuine two-phase state
machine on top of the server's log:

- `ClientIdle` – ready to issue the next request;
- `ClientAwaiting b` – request frame `b` was sent, its response is awaited.

### Key idea: reuse the server by simulating it

The client is implemented as a **predicted server** (it embeds a full
`server_state`) plus a buffer holding the outstanding request's wire bytes. To
predict / validate the response for a request, the client simply runs
`Calc.Server.process_request` on its embedded server. This reuses **every**
verified server handler and the whole `server_exactly` proof, so the client adds
almost no new proof burden.

```fstar
// spec/Calc.Client.Log.fst — abstract client state
noeq type client_state_abs = {
  completed: calc_log;              // predicted-server view of completed round-trips
  pending: option client_frame;     // outstanding request bytes (None = Idle)
}

let client_sent_bytes (st:client_state_abs) : bytes = // requests the client sent
  match st.pending with
  | None   -> st.completed.input_bytes
  | Some b -> Seq.append st.completed.input_bytes b
let client_recv_bytes (st:client_state_abs) : bytes = // responses it received
  st.completed.output_bytes
```

```pulse
// impl/Calc.Client.Types.fst — concrete client
noeq type client_state = { predicted: server_state; pending: Vec.vec U8.t; }
let client_exactly (c:client_state) (st:client_state_abs) : slprop = ...
```

### The two transitions

`impl/Calc.Client.fst` provides the mirror of `new_server`/`process_request`:

- `issue_request` : `Idle → Awaiting`. Writes the request frame into the pending
  buffer and appends it to the sent-byte stream. The one non-trivial obligation
  is that the extended sent stream still parses back to the issued-request list
  (`lemma_client_issue_correspondence`).
- `process_response` : `Awaiting → Idle`. Runs the embedded predicted server on
  the pending request, checks the received bytes equal the predicted response,
  and advances the completed log. Because a fully-`Idle` client's wire
  correspondence *is* just `log_consistent` of its completed log, consistency and
  correspondence come **for free** from the reused server.

Both entry points expose the same style of postcondition as the server: a
`client_single_step` evolution fact plus byte/message/semantic correspondence,
with **0 admits**. This core (state machine + layered-log proof) is verified by
`make verify`; the transport/socket/C-extraction stack is intentionally left to
the server side to keep the client a focused demo.

### Framework instance: `calc_client_state_machine`

Just as the server packages its behaviour as a `Pulse.Lib.Protocol.StateMachine.state_machine`
instance (`Calc.Protocol.calc_frame_state_machine`), the client exposes its own
instance in `Calc.Client.Protocol.fst`:

```fstar
let calc_client_step (st0) (ev) (st1) (out) : GTot prop =
  match ev with
  // Response received from the server → delivered to the application.
  | SM.WireEvent resp ->
      client_recv_step_ok st0 st1 resp /\
      out.so_wire_outputs == [] /\ out.so_local_outputs == [resp]
  // Application issues a request → emitted on the wire.
  | SM.LocalEvent (CalcClientIssue b) ->
      client_issue_step_ok st0 st1 b /\
      out.so_wire_outputs == [b] /\ out.so_local_outputs == []

let calc_client_state_machine : SM.state_machine ... =
  { sm_initial_state = initial_client; sm_step = calc_client_step; }
```

Note the direction flip versus the server: the client's `WireEvent` is a
*received* response and its `so_wire_outputs` are *sent* requests. It reuses the
server's wire format (`calc_frame_wire_format`) — both requests and responses are
5-byte `calc_frame`s. A bridge lemma `lemma_client_single_step_evolves` proves
every `client_single_step` is a one-transition `SM.state_evolves` of this
instance (mirroring the server's
`Calc.Server.CanonicalProtocol.lemma_calc_server_step_rel_state_ahead`), so the
low-level `Calc.Client` operations plug straight into the framework.

---

## Temporal Reasoning: An LTL/CTL Layer over Client–Server Interaction

With both endpoints modelled as state machines, we can reason about their
*interaction over time*. `Pulse.Lib.Protocol.Temporal`, `Calc.System` and
`Calc.System.Temporal` add a small, genuine path-based temporal-logic layer and
prove properties like "the client and server stacks always agree".

### The lag problem

The naive property `AG (client_stack = server_stack)` is **false**: while a
request or response is in flight the stacks disagree by exactly the in-flight
work. (The full TLS stack models the same lag in its `Pairing*` family, where
what one endpoint *sent* is a prefix-extension of what the other *received*.)
The fix is to only compare stacks when the system is **quiescent** (nothing in
flight).

### Combined system (`Calc.System.fst`)

```fstar
type channel_state = Quiet | InReq calc_frame | InResp calc_frame
type system_state  = { client: client_state_abs; server: calc_log; channel }
```

Three transitions (`sys_step`): **issue** (client sends a request → `InReq`),
**serve** (server processes it → `InResp`), **recv** (client receives the
response → `Quiet`). A structural invariant `system_inv` pins down the lag:

- `Quiet` / `InReq`: `server == client.completed` (stacks agree);
- `InResp`: the server is exactly one processed request ahead.

`system_inv` is proved **inductive** (`lemma_inv_preserved`) and therefore holds
on every reachable state (`lemma_reachable_inv`, via `stable_on_closure`). It is
phrased over the logs directly (`==`), reusing the fact that the `recv` step's
`recv_completed` is the *same computation* as the server's `server_process`
(`lemma_recv_completed_eq`) — so no `calc_log` record-equality proofs are needed.

### Generic temporal operators (`Pulse.Lib.Protocol.Temporal.fst`)

Parameterised over an abstract state and step relation, so it is protocol-
independent and lives in the Pulse library (`pulse/lib/pulse/lib/protocol/`) alongside `Pulse.Lib.Protocol.StateMachine` (reusable by
the full TLS stack, not just the calculator demo):

- paths (`path = nat -> state`), runs (`is_run`), suffixes (`shift`);
- LTL operators `holds_G` / `holds_F` / `holds_X` / `holds_U`;
- path quantifiers `ag` (`A G`), `ef`, `af`;
- the **soundness bridge** `lemma_ag_of_invariant`: an inductive invariant true
  on all reachable states entails the genuine path-based `AG`. This lets a cheap
  invariant proof discharge a real temporal property.

### Theorems (`Calc.System.Temporal.fst`)

1. **Flagship safety** — `lemma_flagship_quiescent_agreement`:
   `AG (quiescent ⟹ client_stack = server_stack)`.
2. **A next-step (`X`) property** — `lemma_x_next_is_request`: from an idle,
   quiescent state the *next* state always has a request in flight.
3. **Liveness under fairness** — `lemma_liveness_response_delivered`:
   `AG (in flight ⟹ F quiescent)` — every outstanding request is eventually
   completed. Fairness (no message stays in flight forever) is modelled as an
   eventual strict decrease of a channel rank (Quiet=0, InResp=1, InReq=2); the
   proof chases to quiescence by well-founded recursion on that rank.

---

## Module Reference

### Specification Modules (710 lines)

**Calc.Wire.fst (73 lines)**
- `parse_request : bytes{len==5} -> option request`
- `serialize_response : response -> bytes{len==5}`
- `be_to_n`, `n_to_be` - Big-endian encoding
- Pure spec, unbounded types

**Calc.Wire.Lemmas.fst (142 lines)**
- Arithmetic correctness lemmas
- `lemma_u32_arithmetic_correspondence`
- `lemma_parse_push_value_correct`
- `be_to_n_unrefined` (optional style - refined types work in postconditions too)
- `lemma_be_to_n_equiv`

**Calc.Spec.fst (63 lines)**
- `step : calc_stack -> request -> (calc_stack & response)`
- Pure state machine
- Modular arithmetic matching U32.t
- Errors as transitions (not preconditions)

**Calc.Log.fst (432 lines)**
- `calc_log` type (3-layer structure)
- `log_consistent` predicate
- `log_evolves` preorder
- `log_single_step` relation
- 6 × `step_log_X` functions
- 6 × `lemma_step_log_X_consistent` proofs
- 6 × `lemma_step_log_X_evolves` proofs
- `all_parse` predicate + inductive lemmas

**Calc.Client.Log.fst**
- `client_phase` (`ClientIdle` / `ClientAwaiting`)
- `client_state_abs` type (completed log + optional pending frame)
- `client_sent_bytes` / `client_recv_bytes`
- `client_consistent`, `client_wire_correspondence`
- `client_issue` / `client_recv` transitions
- `client_single_step` relation + `lemma_client_issue_correspondence`

**Calc.Client.Protocol.fst**
- `calc_client_local_event` (`CalcClientIssue`) / `calc_client_local_output`
- `calc_client_step` - client step relation (direction-flipped from server)
- `calc_client_state_machine` - `Pulse.Lib.Protocol.StateMachine.state_machine` instance
- `calc_client_wire_format_state_machine` (reuses `calc_frame_wire_format`)
- `lemma_client_single_step_evolves` - bridge to `SM.state_evolves`

**Pulse.Lib.Protocol.Temporal.fst** (in the Pulse library, protocol-independent)
- Generic path-based temporal logic over `(state, step)`
- `path` / `is_run` / `shift`; operators `holds_G` / `holds_F` / `holds_X` / `holds_U`
- Path quantifiers `ag` (`A G`) / `ef` / `af`
- `lemma_ag_of_invariant` / `lemma_ag_of_inductive` - reachable-invariant ⇒ `AG`

**Calc.System.fst**
- `channel_state` (`Quiet` / `InReq` / `InResp`), `system_state`
- `sys_step` (issue / serve / recv) + `sys_step_stutter`, `initial_system`
- `system_inv` structural invariant; `lemma_inv_preserved`, `lemma_reachable_inv`

**Calc.System.Temporal.fst**
- `lemma_flagship_quiescent_agreement` - `AG (quiescent ⇒ stacks agree)`
- `lemma_x_next_is_request` - `X` next-step property
- `fair` + `lemma_liveness_response_delivered` - `AG (in flight ⇒ F quiescent)`

### Implementation Modules (1092 lines)

**Calc.Impl.Types.fst (42 lines)**
- `server_state` type (Vec-based)
- `server_exactly` predicate (unfoldable)

**Calc.Impl.Parser.fst (41 lines)**
- `parse_tag` - Extract operation tag
- `parse_push_value` - Parse big-endian U32
- Postconditions relate to `be_to_n`

**Operation Handlers (6 × ~110-130 lines)**
- Calc.Impl.Push.fst (122 lines)
- Calc.Impl.Peek.fst (109 lines)
- Calc.Impl.Add.fst (115 lines)
- Calc.Impl.Sub.fst (113 lines)
- Calc.Impl.Mul.fst (115 lines)
- Calc.Impl.Div.fst (133 lines)

Each: `write_*_response` + `process_*` proving `log_single_step`

**Calc.Server.fst (151 lines)**
- `new_server` - Initialize with empty log
- `process_request` - Dispatcher proving `log_single_step`

**Calc.Client.Types.fst**
- `client_state` type (embedded predicted `server_state` + pending Vec)
- `client_exactly` predicate

**Calc.Client.fst**
- `new_client` - Initialize an Idle client
- `issue_request` - `Idle → Awaiting` (mirror of a request write)
- `process_response` - `Awaiting → Idle`, reusing `Calc.Server.process_request`

### Build Infrastructure

**Makefile (67 lines)**
- Incremental verification with `--dep full`
- Parallel extraction (`make -j4`)
- C compilation and testing
- Snapshot management

---

## Extraction to C via KaRaMeL

The verified Pulse code extracts to clean, portable C code via KaRaMeL. This section explains the two-phase extraction process, bundling strategy, and testing workflow.

### Two-Phase Extraction Pipeline

**Phase 1: F* → .krml**
```bash
fstar.exe --codegen krml --extract_module Calc.Server \
  --odir _output impl/Calc.Server.fst
# Produces: _output/Calc_Server.krml
```

**Phase 2: .krml → C**
```bash
krml -tmpdir _extract -skip-compilation \
  -bundle 'Calc.Server=Calc.*[rename=Calc_Server]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims' \
  -no-prefix Calc.Server \
  _output/*.krml
# Produces: _extract/Calc_Server.c, _extract/Calc_Server.h
```

---

### Bundling Strategy

**Goal:** Produce a single `Calc_Server.c/.h` with only `new_server` and `process_request` exposed.

**Bundle 1 - API bundle (what gets exposed in C):**
```makefile
-bundle 'Calc.Server=Calc.*[rename=Calc_Server]'
```

Breakdown:
- `Calc.Server` - API module (public functions in header)
- `=Calc.*` - Include all Calc.* modules in this bundle
- `[rename=Calc_Server]` - Output filename

Result: All Calc.* modules bundled into `Calc_Server.c`, only `Calc.Server` functions public.

**Bundle 2 - Hide bundle (no C output):**
```makefile
-bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
```

These modules are bundled together with NO API module, so they produce no C code. This hides:
- Specification modules (Calc.Wire, Calc.Spec, Calc.Log use unbounded types)
- F* standard library
- Pulse runtime (built into KaRaMeL)

**Name prefix stripping:**
```makefile
-no-prefix Calc.Server
```

Without: `Calc_Server_new_server`, `Calc_Server_process_request`  
With: `new_server`, `process_request`

---

### Type Extraction Rules

**Machine-width types extract directly:**
```pulse
// Pulse
let x: U32.t = ...
let b: U8.t = ...
let s: SZ.t = ...

// C
uint32_t x = ...;
uint8_t b = ...;
size_t s = ...;
```

**Vec extracts to heap allocation:**
```pulse
// Pulse
let stack = Vec.alloc 0ul 0sz;

// C (generated)
uint32_t *stack = KRML_HOST_MALLOC(sizeof(uint32_t) * 0);
```

**Ghost/erased types vanish:**
```pulse
// Pulse
fn process_request (...) (#log0: erased calc_log)

// C (no ghost parameter)
void process_request(...) {
  // log0 does not appear
}
```

**Lemma calls vanish:**
```pulse
// Pulse
Calc.Wire.Lemmas.lemma_be_to_n_equiv ...;
assert (pure (property));

// C (no output)
// Lemmas produce zero code
```

---

### Generated C Code Structure

**Calc_Server.h (public API):**
```c
#ifndef __Calc_Server_H
#define __Calc_Server_H

#include "krmllib.h"
#include "krml/internal/target.h"

// Opaque server state type
typedef struct Calc_Impl_Types_server_state_s Calc_Impl_Types_server_state;

// Public API
Calc_Impl_Types_server_state *new_server(void);

void process_request(
  Calc_Impl_Types_server_state *srv,
  uint8_t *req_buf,
  uint8_t *resp_buf
);

#endif
```

**Calc_Server.c (implementation):**
```c
#include "Calc_Server.h"

// Internal helpers (static)
static uint32_t parse_push_value(uint8_t *buf) { ... }
static void process_push(...) { ... }
// ... other internal functions

// Public API implementations
Calc_Impl_Types_server_state *new_server(void) {
  uint32_t *stack = KRML_HOST_MALLOC(...);
  size_t *count = KRML_HOST_MALLOC(...);
  // ... initialize and return
}

void process_request(...) {
  uint8_t tag = buf[0];
  if (tag == 0) {
    // Push
    uint32_t value = parse_push_value(buf);
    process_push(srv, value, req_buf, resp_buf);
  } else if (tag == 1) {
    // Peek
    process_peek(srv, req_buf, resp_buf);
  }
  // ... other operations
}
```

---

### Heap Allocation Pattern

**Critical lesson:** `Array.alloc` extracts to C **stack allocation**, `Vec.alloc` extracts to C **heap allocation**.

**Wrong (dangling pointers):**
```pulse
fn new_server()
  requires emp
  returns srv: server_state
  ensures ...
{
  let stack = Array.alloc 0ul 0sz;  // C: uint32_t stack[0] on stack
  let count = Array.alloc 0sz 1sz;   // C: size_t count[1] on stack
  {stack; count; ...}                 // Return struct → DANGLING POINTERS
}

// C extraction (BROKEN):
server_state new_server(void) {
  uint32_t stack[0];   // On stack!
  size_t count[1];     // On stack!
  server_state result = {stack, count, ...};
  return result;       // stack and count go out of scope → SEGFAULT
}
```

**Right (heap allocation):**
```pulse
fn new_server()
  requires emp
  returns srv: server_state
  ensures ...
{
  let stack = Vec.alloc 0ul 0sz;    // C: malloc
  let count = Vec.alloc 0sz 1sz;    // C: malloc
  {stack; count; ...}                // Safe to return
}

// C extraction (CORRECT):
server_state *new_server(void) {
  uint32_t *stack = KRML_HOST_MALLOC(sizeof(uint32_t) * 0);
  size_t *count = KRML_HOST_MALLOC(sizeof(size_t) * 1);
  server_state *result = KRML_HOST_MALLOC(sizeof(server_state));
  result->stack = stack;
  result->count = count;
  return result;  // All heap-allocated → safe
}
```

**Pattern:** Use `Vec` for ANY data that must persist beyond the function scope. Use `Box` for heap allocated mutable references.

---

### Build Workflow

**1. Verify Pulse code:**
```bash
make verify
# Uses F* --dep full for incremental, parallel builds
# Output: All modules verified, .checked files in _cache/
```

**2. Extract to .krml:**
```bash
make extract-krml
# Parallel extraction of 9 implementation modules
# Output: 9 .krml files in _output/
```

**3. Run KaRaMeL:**
```bash
make extract-c
# Bundles .krml files, generates C code
# Output: Calc_Server.c, Calc_Server.h in _extract/
```

**4. Compile C code:**
```bash
make test-c
# Compiles with gcc, links with test_main.c
# Runs 9 tests
```

**Full pipeline:**
```bash
make test-c
# Automatically runs: verify → extract-krml → extract-c → compile → test
```

---

### Testing Strategy

**test_main.c structure:**
```c
#include "Calc_Server.h"
#include <assert.h>
#include <string.h>

void test_push_peek() {
  Calc_Impl_Types_server_state *srv = new_server();
  
  uint8_t req[5] = {0, 0, 0, 0, 42};  // Push 42
  uint8_t resp[5];
  
  process_request(srv, req, resp);
  assert(resp[0] == 0);  // OK response
  
  uint8_t peek_req[5] = {1, 0, 0, 0, 0};  // Peek
  process_request(srv, peek_req, resp);
  assert(resp[0] == 1);              // Result response
  assert(resp[4] == 42);             // Value is 42
  
  printf("✅ test_push_peek passed\n");
}

int main() {
  test_push_peek();
  test_add();
  test_div_by_zero();
  // ... 9 tests total
  printf("All tests passed!\n");
  return 0;
}
```

**What the tests verify:**
1. **Functional correctness** - Operations produce correct results
2. **Error handling** - Peek on empty stack returns Error
3. **Modular arithmetic** - Overflow wraps correctly (U32 semantics)
4. **Wire format** - Parsing and serialization work end-to-end
5. **Memory safety** - No leaks, no crashes (verified via valgrind)

---

### Extraction Warnings and Suppressions

**Warning -2: Function not implemented**
```
Warning 2: _zero_for_deref: function not implemented
```

**Cause:** `Pulse.Lib.Pervasives._zero_for_deref` is a Pulse builtin handled specially by KaRaMeL. It has no `.krml` definition but is translated to `*ptr` dereference.

**Solution:** Suppress with `-warn-error -2` (safe for this specific Pulse builtin).

---

**Warning -9: Static initializer needed**
```
Warning 9: some_constant will be initialized in krmlinit_globals()
```

**Cause:** A global constant (e.g., struct with default values) cannot be a C compile-time constant. KaRaMeL generates `krmlinit_globals()` to initialize it at runtime.

**Solution:** Suppress with `-warn-error -9` if `krmlinit_globals()` is called before use (or not needed).

---

**Warning -17: Static initializer declaration**
```
Warning 17: declaration that triggered krmlinit
```

**Cause:** Consequence of warning 9 - shows which declaration triggered runtime initialization.

**Solution:** Suppress with `-warn-error -17` (same conditions as -9).

---

**DO NOT suppress warnings blindly!** Run KaRaMeL without `-warn-error` first to see what warnings are emitted. Warnings like -4 (type error) or -6 (VLA) indicate real problems.

---

### Complete Makefile Targets

```bash
# Verification only
make verify              # Incremental verification
make -j4 verify          # Parallel verification

# Extraction
make extract-krml        # F* → .krml (phase 1)
make extract-c           # .krml → C (phase 2)
make extract             # Both phases

# Testing
make test-c              # Full pipeline: verify → extract → compile → test

# Utilities
make check-admits        # Verify 0 admits
make stats               # Show LOC, module counts
make clean               # Remove build artifacts
```

---

### Incremental Build Support

The Makefile uses `--dep full` for proper dependency tracking:

```makefile
.depend: $(ALL_FILES)
	$(FSTAR) --dep full $(ALL_FILES) --output_deps_to $@

-include .depend
```

**Benefits:**
- Only changed files are reverified
- Parallel builds work correctly (`make -j4`)
- .krml extraction is parallelized
- Dependency order is automatic

**Example:**
```bash
# Change Calc.Impl.Push.fst
make -j4 verify

# Only rebuilds:
# - Calc.Impl.Push.fst (changed)
# - Calc.Server.fst (depends on Push)
# Other modules use cached .checked files
```

---

## Applying to TLS 1.3

The **layered log specification pattern** provides:

1. **End-to-end correctness:** Wire bytes ↔ Messages ↔ State transitions all proven
2. **Modularity:** Each handler proves local property, dispatcher composes
3. **Automatic correspondence:** Fold/unfold server_exactly maintains log_consistent
4. **Scalability:** 2183 lines, 0 admits, 12-second verification

**Core components:**
- **Ghost log** with 3-layer structure (wire/message/semantic)
- **log_consistent** predicate connecting all layers
- **server_exactly** relating ghost log to concrete heap
- **Modular handlers** each proving log_single_step
- **Arithmetic lemmas** connecting implementation to spec

**Reusable for:** TLS 1.3, database protocols, distributed systems, any stateful protocol requiring complete functional correctness proofs.

### Mapping the calc pattern to TLS

| Calc sample | TLS client |
| --- | --- |
| `Calc.Wire` request/response bytes | TLS records, handshake messages, alerts, and application-data bytes in `TLS13.Wire.Spec` |
| `Calc.Spec.step` over stack requests | TLS client state-machine transitions in `TLS13.Spec.StateMachine` |
| `Calc.Log.log_consistent` | `TLS13.ConnectionLog.connection_view_consistent` tying buffers to records, messages, traces, and app projection |
| `server_exactly` | A Pulse `client_core`/connection predicate relating heap state to a ghost connection view |
| `process_request` with input/output buffers | TLS buffer-oriented `process_request` over network/app input buffers and network/app output buffers |
| Modular handler lemmas | Handshake, record, app-data, close, and failure-step preservation lemmas |

The key design lesson for TLS is to keep live socket I/O outside the verified
core theorem. The calc server proves one request/response buffer step at a time;
TLS should do the same with explicit network/application buffers, while an
external driver relates those buffers to actual socket reads and writes.

### Current calc validation commands

```sh
cd calc_sample
make verify
make check-admits
make test-c
```

`make check-admits` is the guard that the calc methodology reference remains
admit-free.

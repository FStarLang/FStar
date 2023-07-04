# Building a Verified DPE in Pulse

June 30th, 2023


## Introduction

This document describes a milestone in the work on building a verified DPE (DICE Protection 
Environment) implementation in Pulse. The progress presented here is a basic DICE Engine and 
DICE Layer 0 in Pulse. The implementation is based on a DICE implementationin in Low* called
[DICE*](https://github.com/verified-HRoT/dice-star) (dice-star). 
The new contribution is organized as follows

```
engine/
  EngineCore.fst  (* main engine logic *)
  EngineTypes.fst (* abstraction of L0 types *)
l0/
  L0Core.fst      (* main L0 logic *)
  L0Crypto.fst    (* L0 crypto helpers *)
  L0Types.fst     (* abstraction of L0 types *)
  X509.fst        (* abstraction of X509 API *)
common/
  HACL.fst        (* abstraction of HACL* API *)
```


## About the Implementation

The engine and L0 implementations in Pulse correspond to 
[dice-star/src/dice_engine](https://github.com/verified-HRoT/dice-star/tree/main/src/dice_engine)
and [dice-star/src/l0](https://github.com/verified-HRoT/dice-star/tree/main/src/l0),
from DICE*. A record type is defined per layer to maintain program state, these defintions
are located in `EngineTypes.fst` and `L0Types.fst`. The main logic for each layer are 
located in `EngineCore.engine_main` and `L0Core.l0_main`. 

Pulse, being a separation logic, simplifies much of the manual verification necessary
in the DICE* implementation by eradicating the need for the programmer to explicitly
reason about the heap. Instead, the programmer reasons about permissions on program
state. The separation logic does away with the need for proofs about the non-mutation
and disjointness of program state by forcing the programmer to be explict about mutation
in the specification and requiring that distinct pieces of owned program state are
disjoint. 


## Limitations

The Pulse implementation of DICE engine and DICE L0
- allocates heap arrays instead of stack arrays,
- doesn't model stack erasure,
- doesn't model public vs. secret data,
- abstracts HACL*/X509/ASN1 types to basic F* types, and
- doesn't implement HACL* and X509 primitives.


## Next Steps

Current work is to make the described DICE implementation DPE-compatible and build
a DPE in Pulse. This requires refactoring the implementation into the DPE API. 
For context, the DPE hides critical data from the client by maintaining persistent state between
DICE layer invocations. This way, the DPE can produce attestation materials for a
client without letting the client interact with critical device secrets/intermediary
state. Relevant considerations for building a DPE are
- what the DPE "context" should look like -- the context is the persistent DPE state
- how to manage sessions and contexts-per-session

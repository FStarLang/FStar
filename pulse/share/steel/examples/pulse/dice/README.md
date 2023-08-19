# Verified DPE in Pulse

This directory hosts Megan's Summer 2023 work building a verified DPE (DICE Protection 
Environment) in Pulse. The implementation of the DICE Engine and Layer 0 is based 
on a verified DICE implementationin in Low* called [DICE*](https://github.com/verified-HRoT/dice-star) 
(dice-star). The implementation of a DPE is based on the 
[DPE specification](https://trustedcomputinggroup.org/wp-content/uploads/TCG-DICE-Protection-Environment-Specification_14february2023-1.pdf)
provided by the Trusted Computing Group. 

Auxiliary to this work are [array](https://github.com/FStarLang/steel/blob/megan_dpe/share/steel/examples/pulse/lib/Pulse.Lib.Array.fsti) 
and [hash table](https://github.com/FStarLang/steel/blob/megan_dpe/share/steel/examples/pulse/lib/Pulse.Lib.HashTable.fsti) libraries in Pulse. 
Megan's contributions are organized as follows.

```
dpe/
  DPETypes.fsti               (* types for DPE state *)
  DPE.fst(i)                  (* DPE commands *)
engine/
  EngineTypes.fst(i)          (* types for engine state *)
  EngineCore.fst              (* engine logic *)
l0/
  L0Types.fst(i)              (* types for layer 0 state *)
  L0Crypto.fst                (* layer 0 crypto *)
  L0Core.fst                  (* layer 0 logic *)
  X509.fst                    (* abstraction of X509 API *)
common/
  HACL.fst                    (* abstraction of HACL* API *)
../lib/
  Pulse.Lib.Array.fst(i)      (* array utilities *)
  Pulse.Lib.HashTable.fst(i)  (* hash table utilities *)
```

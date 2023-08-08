# Building a Verified DPE in Pulse

This directory hosts Megan's Summer 2023 work building a verified DPE (DICE Protection 
Environment) in Pulse. The implementation of the DICE Engine and Layer 0 is based 
on a verified DICE implementationin in Low* called [DICE*](https://github.com/verified-HRoT/dice-star) 
(dice-star). The implementation of a DPE is based on the 
[DPE specification](https://trustedcomputinggroup.org/wp-content/uploads/TCG-DICE-Protection-Environment-Specification_14february2023-1.pdf)
provided by the Trusted Computing Group. 

Auxiliary to this work are array and hash table libraries in Pulse. 
Megan's contributions are organized as follows.

```
dpe/
  DPE.fst(i)                  (* DPE logic *)
engine/
  EngineCore.fst              (* engine logic *)
  EngineTypes.fst(i)          (* abstraction of engine types *)
l0/
  L0Core.fst                  (* main L0 logic *)
  L0Crypto.fst                (* L0 crypto functions *)
  L0Types.fst(i)              (* abstraction of L0 types *)
  X509.fst                    (* abstraction of X509 API *)
common/
  HACL.fst                    (* abstraction of HACL* API *)
../lib/
  Pulse.Lib.Array.fst(i)      (* array utilities *)
  Pulse.Lib.HashTable.fst(i)  (* hash table utilities *)
```
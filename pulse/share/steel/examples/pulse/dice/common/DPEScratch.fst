module DPEScratch
module A = Steel.ST.Array
module PM = Pulse.Main
open Steel.ST.Util 
open Steel.ST.Array
open Steel.FractionalPermission
open FStar.Ghost
open Pulse.Steel.Wrapper
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32


(* 

DICE Engine 
-----------
inputs: L0 binary
outputs: CDI


DICE L0
-----------
inputs: FWID, CDI
outputs: AliasKey_priv, Cert_AliasKey, CSR_DeviceID

DICE L1
-------
inputs: AliasKey_priv, Cert_AliasKey, CSR_DeviceID
outputs: None

*)

noeq
type context = 
  | Engine_context  : uds:A.array U8.t -> 
                      context
  | L0_context      : cdi:A.larray U8.t 32 -> 
                      context
  | L1_context      : aliasKey_priv:A.larray U8.t 32 ->
                      cert_aliasKey:A.array U8.t ->
                      csr_deviceID:A.array U8.t ->
                      context

// all other state is local to its corresponding layer and can be 
// destroyed when the layer exits

(* 

might be nice to have something like

init_engine_record (uds) (l0_image) : engine_record_t
init_l0_record (cdi) (fwid) : l0_record_t

*)
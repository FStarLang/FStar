module L0Types
open Pulse.Steel.Wrapper
open Steel.ST.Util 
open Steel.ST.Array
open Steel.FractionalPermission
open FStar.Ghost
module R = Steel.ST.Reference
module A = Steel.ST.Array
module T = FStar.Tactics
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open Array
open HACL

let x509_version_t : Type0 = admit()

let x509_serialNumber_t : Type0 = admit()

let deviceIDCRI_t : Type0 = admit()

let deviceIDCSR_t (len: US.t) : Type0 = admit()

let aliasKeyTBS_t : Type0 = admit()

let aliasKeyCRT_t (len: US.t) : Type0 = admit()

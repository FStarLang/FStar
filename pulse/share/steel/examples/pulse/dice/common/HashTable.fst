module HashTable
open Pulse.Main
open Pulse.Steel.Wrapper
open FStar.Ghost
open Steel.ST.Util
open Steel.FractionalPermission
module R = Steel.ST.Reference
module A = Steel.ST.Array
module L = Steel.ST.SpinLock
module US = FStar.SizeT
module U32 = FStar.UInt32
open LinearScanHashTable
open PulseHashTable

let mk_pht_sig keyt valt hashf = { keyt; valt; hashf }

let mk_ht (#s:pht_sig) (sz:pos_us) (contents:A.larray (cell s.keyt s.valt) (US.v sz))
  : ht_t s
  = { sz; contents; }

let ht_perm (s:pht_sig) (ht: ht_t s) : vprop
  = exists_ (fun s -> A.pts_to ht.contents full_perm s)

type locked_ht_t (s:pht_sig) (pht:pht s) = ht:ht_t s & L.lock (models s ht pht)

// Hash table interface

assume val new_table (#s:pht_sig) : ht_t s

assume val store (#s:pht_sig) (ht:ht_t s) (k:s.keyt) (v:s.valt) : unit

assume val get (#s:pht_sig) (ht:ht_t s) (k:s.keyt) : s.valt

assume val delete (#s:pht_sig) (ht:ht_t s) (k:s.keyt) : unit

assume val destroy (#s:pht_sig) (ht:ht_t s) : unit

// Session ID types

type sid_ref_t = r:R.ref nat & L.lock (exists_ (fun n -> R.pts_to r full_perm n))

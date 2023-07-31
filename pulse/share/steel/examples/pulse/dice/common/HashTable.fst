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

let mk_pht_sig_us keyt valt hashf : pht_sig_us = { keyt; valt; hashf }

let mk_ht (#s:pht_sig_us) (sz:pos_us) (contents:A.larray (cell s.keyt s.valt) (US.v sz))
  : ht_t s
  = { sz; contents; }

let mk_init_pht (#s:pht_sig_us) (sz:pos_us)
  : pht_t (s_to_ps s)
  = 
  { sz = US.v sz;
    spec = (fun (k:s.keyt) -> None);
    repr = Seq.create (US.v sz) Clean;
    inv = (); }

let ht_perm (s:pht_sig_us) (ht: ht_t s) : vprop
  = exists_ (fun (pht:pht_t (s_to_ps s)) -> models s ht pht)

type locked_ht_t (s:pht_sig_us) = ht:ht_t s & L.lock (ht_perm s ht)

// Hash table interface

assume val new_table (#s:pht_sig_us) : ht_t s

assume val store (#s:pht_sig_us) (ht:ht_t s) (k:s.keyt) (v:s.valt) : unit

assume val get (#s:pht_sig_us) (ht:ht_t s) (k:s.keyt) : s.valt

assume val delete (#s:pht_sig_us) (ht:ht_t s) (k:s.keyt) : unit

assume val destroy (#s:pht_sig_us) (ht:ht_t s) : unit

// Session ID types

type sid_ref_t = r:R.ref nat & L.lock (exists_ (fun n -> R.pts_to r full_perm n))

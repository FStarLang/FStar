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

// Hash table types 

noeq
type cell (kt:eqtype) (vt:Type0) =
  | Clean
  | Zombie
  | Used : k:kt -> v:vt -> cell kt vt

noeq
type ht_sig = {
  sz : pos;
  kt : eqtype;
  vt : Type0;
  hashf : kt -> nat;
}

let mk_ht_sig sz kt vt hashf = { sz; kt; vt; hashf }

noeq
type ht_t (s:ht_sig) = {
  contents : A.larray (cell s.kt s.vt) s.sz;
}

// check out ephemeral ht itf
type ht_ref_t (s:ht_sig) = r:R.ref (ht_t s) & L.lock (exists_ (fun ht -> R.pts_to r full_perm ht))

// Hash table interface

assume val new_table (#s:ht_sig) : ht_t s

assume val store (#s:ht_sig) (ht:ht_t s) (k:s.kt) (v:s.vt) : unit

assume val get (#s:ht_sig) (ht:ht_t s) (k:s.kt) : s.vt

assume val delete (#s:ht_sig) (ht:ht_t s) (k:s.kt) : unit

assume val destroy (#s:ht_sig) (ht:ht_t s) : unit

// Session ID types

type sid_ref_t = r:R.ref nat & L.lock (exists_ (fun n -> R.pts_to r full_perm n))

module Pulse.Lib.HashTable
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module LK = Pulse.Lib.SpinLock
module PHT = LinearScanHashTable
open LinearScanHashTable
open Pulse.Class.BoundedIntegers

type pos_us = n:US.t{US.v n > 0}

noeq
type pht_sig_us = {
  keyt : eqtype;
  valt : Type0;
  hashf : keyt -> US.t;
}
let mk_pht_sig_us keyt valt hashf : pht_sig_us = { keyt; valt; hashf }
let mk_used_cell #a #b (k:a) (v:b) = Used k v

noeq
type ht_t (s : pht_sig_us) = {
  sz : pos_us;
  contents : A.larray (cell s.keyt s.valt) (US.v sz);
}
let mk_ht (#s:pht_sig_us) (sz:pos_us) 
          (contents:A.larray (cell s.keyt s.valt) (US.v sz))
  : ht_t s 
  = { sz; contents; }

let s_to_ps (s:pht_sig_us) : pht_sig
  = { keyt = s.keyt; valt = s.valt; hashf = (fun k -> US.v (s.hashf k)) }

let mk_init_pht (#s:pht_sig_us) (sz:pos_us)
  : pht_t (s_to_ps s)
  = 
  { sz = US.v sz;
    spec = (fun (k:s.keyt) -> None);
    repr = Seq.create (US.v sz) Clean;
    inv = (); }

val models (s:pht_sig_us) (ht:ht_t s) (pht:pht_t (s_to_ps s)) : vprop

type locked_ht_t (s:pht_sig_us) = ht:ht_t s & LK.lock (exists_ (fun pht -> models s ht pht))

let pht_sz #s (pht:pht_t s) : pos = pht.sz

let destroy_val_fn_t (t:Type0) : Type = v:t -> stt unit emp (fun _ -> emp) 


val alloc_locked (#s:pht_sig_us) (l:pos_us)
  : stt (locked_ht_t s) emp (fun _ -> emp)

val dealloc (#s:pht_sig_us) (ht:ht_t s) (l:pos_us) (destroy_val:destroy_val_fn_t s.valt)
  : stt unit (requires exists_ (fun pht -> models s ht pht))
             (ensures fun _ -> emp)

val lookup (#s:pht_sig_us)
           (#pht:erased (pht_t (s_to_ps s)))
           (ht:ht_t s) (k:s.keyt)
  : stt (bool & option s.valt)
    (models s ht pht)
    (fun p -> models s ht pht ** pure ( fst p ==> (snd p) == PHT.lookup pht k ))

let maybe_update (b:bool) (s:pht_sig_us) (ht:ht_t s) (pht pht':pht_t (s_to_ps s)) =
  if b then models s ht pht' else models s ht pht

val insert (#s:pht_sig_us)
          (#pht:(p:erased (pht_t (s_to_ps s)){PHT.not_full p.repr}))
          (ht:ht_t s) (k:s.keyt) (v:s.valt)
  : stt bool 
    (models s ht pht)
    (fun b -> maybe_update b s ht pht (PHT.insert pht k v))

val delete (#s:pht_sig_us)
          (#pht:erased (pht_t (s_to_ps s)))
          (ht:ht_t s) (k:s.keyt)
  : stt bool
    (models s ht pht)
    (fun b -> maybe_update b s ht pht (PHT.delete pht k))

val not_full (#s:pht_sig_us) (#pht:erased (pht_t (s_to_ps s))) (ht:ht_t s)
  : stt bool
    (models s ht pht)
    (fun b -> 
      models s ht pht ** 
      pure (b ==> PHT.not_full #(s_to_ps s) #(pht_sz pht) pht.repr))
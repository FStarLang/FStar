module PulseHashTable
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

let models (s:pht_sig_us) (ht:ht_t s) (pht:pht_t (s_to_ps s)) : vprop
= A.pts_to ht.contents full_perm pht.repr **
  pure (
    US.v ht.sz == pht.sz /\
    A.is_full_array ht.contents
  )

let ht_perm (s:pht_sig_us) (ht: ht_t s) : vprop
  = exists_ (fun (pht:pht_t (s_to_ps s)) -> models s ht pht) // FIXME: this is erasing the pht

type locked_ht_t (s:pht_sig_us) = ht:ht_t s & LK.lock (ht_perm s ht)

let canonical_index_us (#s:pht_sig_us) (k:s.keyt) (sz:pos_us) 
  : US.t = s.hashf k % sz

let modulo_us (v1 v2:US.t) (m:pos_us) (_:squash(US.fits (US.v v1 + US.v v2)))
  : US.t 
  = (v1 + v2) % m

let pht_sz #s (pht:pht_t s) : pos = pht.sz



val lookup (#s:pht_sig_us)
          (#pht:erased (pht_t (s_to_ps s)))
          (ht:ht_t s) (k:s.keyt)
  : stt (o:option s.valt{o == PHT.lookup pht k})
    (models s ht pht)
    (fun _ -> models s ht pht)

val insert (#s:pht_sig_us)
          (#pht:(p:erased (pht_t (s_to_ps s)){PHT.not_full p.repr}))
          (ht:ht_t s) (k:s.keyt) (v:s.valt)
  : stt unit 
    (models s ht pht)
    (fun _ -> models s ht (PHT.insert pht k v))

val delete (#s:pht_sig_us)
          (#pht:erased (pht_t (s_to_ps s)))
          (ht:ht_t s) (k:s.keyt)
  : stt unit
    (models s ht pht)
    (fun _ -> models s ht (PHT.delete pht k))

val not_full (#s:pht_sig_us) (#pht:erased (pht_t (s_to_ps s))) (ht:ht_t s)
  : stt bool
    (models s ht pht)
    (fun b -> 
      models s ht pht ** 
      pure (b ==> PHT.not_full #(s_to_ps s) #(pht_sz pht) pht.repr))
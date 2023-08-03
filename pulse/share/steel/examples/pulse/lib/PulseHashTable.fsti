module PulseHashTable
module PM = Pulse.Main
open Steel.ST.Array
open Steel.FractionalPermission
open Steel.ST.Util
open FStar.Ghost
open Pulse.Steel.Wrapper
module A = Steel.ST.Array
module R = Steel.ST.Reference
module US = FStar.SizeT
module U8 = FStar.UInt8
module LK = Steel.ST.SpinLock
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
= A.pts_to ht.contents full_perm pht.repr `star`
  pure (
    US.v ht.sz == pht.sz /\
    A.is_full_array ht.contents
  )

let ht_perm (s:pht_sig_us) (ht: ht_t s) : vprop
  = exists_ (fun (pht:pht_t (s_to_ps s)) -> models s ht pht)

type locked_ht_t (s:pht_sig_us) = ht:ht_t s & LK.lock (ht_perm s ht)

let pht_sz #s (pht:pht_t s) : pos = pht.sz


val lookup (#s:pht_sig_us)
           (#pht:erased (pht_t (s_to_ps s)))
           (ht:ht_t s) (k:s.keyt)
  : stt (bool & option s.valt)
    (models s ht pht)
    (fun p -> models s ht pht `star` pure ( fst p ==> (snd p) == PHT.lookup pht k ))

val insert (#s:pht_sig_us)
          (#pht:(p:erased (pht_t (s_to_ps s)){PHT.not_full p.repr}))
          (ht:ht_t s) (k:s.keyt) (v:s.valt)
  : stt bool 
    (models s ht pht)
    (fun b -> match b with 
              | true -> models s ht (PHT.insert pht k v)
              | false -> models s ht pht)

val delete (#s:pht_sig_us)
          (#pht:erased (pht_t (s_to_ps s)))
          (ht:ht_t s) (k:s.keyt)
  : stt bool
    (models s ht pht)
    (fun b -> match b with 
              | true -> models s ht (PHT.delete pht k)
              | false -> models s ht pht)

val not_full (#s:pht_sig_us) (#pht:erased (pht_t (s_to_ps s))) (ht:ht_t s)
  : stt bool
    (models s ht pht)
    (fun b -> 
      models s ht pht `star` 
      pure (b ==> PHT.not_full #(s_to_ps s) #(pht_sz pht) pht.repr))
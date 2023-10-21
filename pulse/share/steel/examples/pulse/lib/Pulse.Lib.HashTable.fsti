module Pulse.Lib.HashTable
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module PHT = Pulse.Lib.HashTable.Spec
open Pulse.Lib.HashTable.Spec

type pos_us = n:US.t{US.v n > 0}

let mk_used_cell (#a:eqtype) #b (k:a) (v:b) : cell a b = Used k v

noeq
type ht_t (keyt:eqtype) (valt:Type) = {
  sz : pos_us;
  hashf: keyt -> US.t;
  contents : A.larray (cell keyt valt) (US.v sz);
}

let mk_ht (#k:eqtype) #v 
          (sz:pos_us) 
          (hashf:k -> US.t)
          (contents:A.larray (cell k v) (US.v sz))
  : ht_t k v
  = { sz; hashf; contents; }

let lift_hash_fun (#k:eqtype) (hashf:k -> US.t) : k -> nat = fun k -> US.v (hashf k)

let mk_init_pht (#k:eqtype) #v (hashf:k -> US.t) (sz:pos_us)
  : GTot (pht_t k v)
  = 
  { spec = (fun k -> None);
    repr = {
      sz=US.v sz;
      seq=Seq.create (US.v sz) Clean;
      hashf=lift_hash_fun hashf;
    };
    inv = (); }

val models #k #v (ht:ht_t k v) (pht:pht_t k v) : vprop

let pht_sz #k #v (pht:pht_t k v) : GTot pos = pht.repr.sz


val test_mono (_:unit) : stt unit emp (fun _ -> emp)
// let maybe_update #kt #vt (b:bool) (ht:ht_t kt vt) (pht pht':pht_t kt vt)
//   : vprop
//   = if b then models ht pht' else models ht pht

// val insert (#kt:eqtype) (#vt:Type0)
//            (#pht:(p:erased (pht_t kt vt){PHT.not_full p.repr}))
//            (ht:ht_t kt vt) (k:kt) (v:vt)
//   : stt bool 
//     (models ht pht)
//     (fun b -> maybe_update b ht pht (PHT.insert pht k v))

// val delete (#kt:eqtype) (#vt:Type0)
//            (#pht:erased (pht_t kt vt))
//            (ht:ht_t kt vt) (k:kt)
//   : stt bool
//     (models ht pht)
//     (fun b -> maybe_update b ht pht (PHT.delete pht k))

// val not_full (#kt:eqtype) (#vt:Type0)
//              (#pht:erased (pht_t kt vt))
//              (ht:ht_t kt vt)
//   : stt bool
//     (models ht pht)
//     (fun b -> 
//       models ht pht ** 
//       pure (b ==> PHT.not_full pht.repr))
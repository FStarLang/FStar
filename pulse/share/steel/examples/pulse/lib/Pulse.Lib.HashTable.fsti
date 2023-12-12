module Pulse.Lib.HashTable
open Pulse.Lib.Pervasives
module V = Pulse.Lib.Vec
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
  contents : V.vec (cell keyt valt);
}

let mk_ht (#k:eqtype) #v 
          (sz:pos_us) 
          (hashf:k -> US.t)
          (contents:V.vec (cell k v))
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

val alloc (#k:eqtype) (#v:Type0) (hashf:k -> US.t) (l:pos_us)
  : stt (ht_t k v) emp 
        (fun ht ->
          exists* pht.
            models ht pht **
            pure (pht == mk_init_pht hashf l))

val dealloc (#k:eqtype) (#v:Type0) (ht:ht_t k v)
  : stt unit (requires exists* pht. models ht pht)
             (ensures fun _ -> emp)

val lookup (#kt:eqtype) (#vt:Type0)
  (r:ref (ht_t kt vt))
  (k:kt)
  (#ht:erased (ht_t kt vt))
  (#pht:erased (pht_t kt vt))
  : stt (bool & option vt)
    (pts_to r ht ** models ht pht)
    (fun p -> pts_to r ht ** models ht pht ** pure (fst p ==> (snd p) == PHT.lookup pht k ))

val insert (#kt:eqtype) (#vt:Type0)
           (ht:ht_t kt vt) (k:kt) (v:vt)
           (#pht:erased (pht_t kt vt){PHT.not_full pht.repr})
  : stt bool 
        (models ht pht)
        (fun b -> 
          exists* pht'.
            models ht pht' **
            pure (if b
                  then pht'==PHT.insert pht k v
                  else pht'==reveal pht))


val delete (#kt:eqtype) (#vt:Type0)
           (ht:ht_t kt vt) (k:kt)
           (#pht:erased (pht_t kt vt))
  : stt bool
    (models ht pht)
    (fun b -> 
        exists* pht'.
            models ht pht' **
            pure (if b
                  then pht'==PHT.delete pht k
                  else pht'==reveal pht))

val not_full (#kt:eqtype) (#vt:Type0)
             (ht:ht_t kt vt)
             (#pht:erased (pht_t kt vt))
  : stt bool (models ht pht)
      (fun b -> 
        models ht pht ** 
        pure (b ==> PHT.not_full pht.repr))

val test_mono () : stt unit emp (fun _ -> emp)
